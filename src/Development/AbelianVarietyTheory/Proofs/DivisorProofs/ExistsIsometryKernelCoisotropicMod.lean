module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrMod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrMod
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_cell_section : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  intro E _ _ _ H D X _ _ _ y n N hn hN Z Z' h hker hsurj
  haveI := D.proj
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hN
    omega
  let mulN : X →ₗ[𝓞 E] X := N • LinearMap.id
  have hinj : Function.Injective mulN := by
    intro u v huv
    have h1 : N • u = N • v := by simpa [mulN] using huv
    have h2 : (N : ℤ) • (u - v) = 0 := by
      rw [smul_sub, natCast_zsmul, natCast_zsmul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact absurd (by exact_mod_cast h3) hN0
    · exact sub_eq_zero.1 h3
  let q : D.La →ₗ[𝓞 E] D.La := LinearMap.id - Z'.subtype ∘ₗ h.proj
  have hqa : ∀ a, q a = a - (h.proj a : D.La) := fun a => rfl
  have hq : ∀ a, q a ∈ perp D Z := fun a => by rw [hqa]; exact h.sub_proj_mem a
  have hrange : ∀ a, (y ∘ₗ q) a ∈ LinearMap.range mulN := fun a => by
    obtain ⟨e, he⟩ := (hker (q a)).2 ⟨q a, hq a, 0, by simp⟩
    exact ⟨e, by simp [mulN, he]⟩
  let ε : D.La →ₗ[𝓞 E] X :=
    (LinearEquiv.ofInjective mulN hinj).symm.toLinearMap ∘ₗ (y ∘ₗ q).codRestrict _ hrange
  have hε : ∀ a, N • ε a = y (q a) := by
    intro a
    have h2 := congrArg Subtype.val ((LinearEquiv.ofInjective mulN hinj).apply_symm_apply ⟨(y ∘ₗ q) a, hrange a⟩)
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let muln : X →ₗ[𝓞 E] X := n • LinearMap.id
  let S : Submodule (𝓞 E) X := LinearMap.range muln
  let g : Z' →ₗ[𝓞 E] X ⧸ S := S.mkQ ∘ₗ y ∘ₗ Z'.subtype
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨x, rfl⟩ := S.mkQ_surjective x
    obtain ⟨b, hb, e, he⟩ := hsurj x
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.mkQ_apply, he]
    rw [Submodule.Quotient.eq]
    exact ⟨e, by simp [mulN, muln]⟩
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g (S.mkQ ∘ₗ ε) hg
  have hs' : ∀ a, ∃ e, y (s a) = ε a + n • e := by
    intro a
    have h1 := LinearMap.congr_fun hs a
    simp only [g, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.subtype_apply] at h1
    rw [Submodule.Quotient.eq] at h1
    obtain ⟨e, he⟩ := h1
    refine ⟨e, ?_⟩
    have he' : n • e = y (s a) - ε a := by simpa [muln] using he
    rw [he']
    abel
  refine ⟨Z'.subtype ∘ₗ h.proj + N • (Z'.subtype ∘ₗ s ∘ₗ q), fun a => ?_, fun b hb => ?_, fun a => ?_, fun a => ?_⟩
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
    exact add_mem (h.proj a).2 (Z'.nsmul_mem (s (q a)).2 N)
  · have hqb : q b = 0 := by rw [hqa, h.proj_of_mem hb, sub_self]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, hqb,
      map_zero, ZeroMemClass.coe_zero, smul_zero, add_zero]
    exact h.proj_of_mem hb
  · obtain ⟨e, he⟩ := hs' (q a)
    refine ⟨N • e, ?_⟩
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, map_add (f := _),
      map_nsmul]
    have hy : y (q a) = y a - y (h.proj a) := by rw [hqa, map_sub]
    have hqq : q (q a) = q a := by rw [hqa (q a), h.proj_of_perp (hq a), sub_zero]
    rw [he, smul_add, hε, hqq, hy, smul_comm N n e]
    abel
  · refine ⟨(h.proj a : D.La) - a, ?_, s (q a), ?_⟩
    · have := neg_mem (h.sub_proj_mem a)
      rwa [neg_sub] at this
    · simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply]
      abel

end GlobalTheory.LowFilt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrModStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_section_opposite_congr_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ σ : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') ∧ (∀ b ∈ Z', σ b = b) ∧ (∀ a, ∃ e, y (σ a) = y a + n • e) ∧
      ∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e := by
  first | exact @GlobalTheory.LowFilt.exists_cell_section | exact GlobalTheory.LowFilt.exists_cell_section | (intros; apply GlobalTheory.LowFilt.exists_cell_section <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem ker_mod_eq_perp_range_add : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ y n hn Z Z' h hsurj t ht hiso hdiv a
  have hW : IsOpp D (LinearMap.range t) Z' := (h.symm.shear t ht hiso).symm

  have hdivZ : ∀ b ∈ Z', (∀ z : Z, (n : ℤ) ∣ D.EF (t z) b) → ∃ b'', b = n • b'' := by
    intro b hb hbd
    have hx : ∀ x : LinearMap.range t, (n : ℤ) ∣ D.EF x b := by
      rintro ⟨_, z, rfl⟩
      exact hbd z
    let φ : LinearMap.range t →+ ℤ := AddMonoidHom.mk' (fun x => D.EF x b / n) fun x x' => by
      simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]
      exact Int.add_ediv_of_dvd_left (hx x)
    obtain ⟨b'', hb'', -⟩ := hW.2.2.1 φ
    refine ⟨b'', ?_⟩
    have h0 : (n • (b'' : D.La)) - b = 0 := by
      refine hW.eq_zero (sub_mem (Z'.nsmul_mem b''.2 n) hb) fun w hw => ?_
      have e1 := hb'' ⟨w, hw⟩
      simp only [φ, AddMonoidHom.mk'_apply] at e1
      have e2 : (n : ℤ) ∣ D.EF w b := hx ⟨w, hw⟩
      rw [ef_swap, map_sub, map_nsmul, e1, nsmul_eq_mul, Int.mul_ediv_cancel' e2]
      simp
    exact (sub_eq_zero.1 h0).symm
  have hperp0 : ∀ (k : D.La), k ∈ perp D (LinearMap.range t) → ∀ z : Z, D.EF (t z) k = 0 := by
    intro k hk z
    rw [ef_swap, hk _ ⟨z, rfl⟩, neg_zero]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hk⟩ := hW.exists_sub_mem_perp a
    obtain ⟨b'', hb''⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z a ⟨e, he⟩
      have h2 : D.EF (t z) b = D.EF (t z) a - D.EF (t z) (a - b) := by
        rw [map_sub]; ring
      rw [h2, hperp0 _ hk z, sub_zero]
      exact h1
    refine ⟨a - b, hk, b'', ?_⟩
    rw [← hb'', sub_add_cancel]
  · rintro ⟨k, hk, e, rfl⟩
    obtain ⟨b, hb, e₁, hb1⟩ := hsurj (y k)
    obtain ⟨b'', rfl⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z (k - b) ⟨-e₁, by rw [map_sub, hb1, smul_neg]; abel⟩
      rw [map_sub, hperp0 _ hk z, zero_sub, Int.dvd_neg] at h1
      exact h1
    refine ⟨y b'' - e₁ + y e, ?_⟩
    rw [map_nsmul] at hb1
    rw [map_add (f := _), map_nsmul, smul_add, smul_sub, hb1]
    abel

end GlobalTheory.LowFilt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmulStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | exact GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | (intros; apply GlobalTheory.LowFilt.ker_mod_eq_perp_range_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add (f := _), map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add (f := _), hc, map_sub, LinearMap.sub_apply, map_add (f := _)]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShearStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_extending_isotropic_shear : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ), 0 < N → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' → ∀ t : Z →ₗ[𝓞 E] D.La,
    (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) → (∀ z z' : Z, D.EF (t z) (t z') = 0) →
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧ ∀ z : Z, g z = t z := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | exact GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_isometry_extend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjoint
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem exists_eq_nsmul_of_forall_ef_dvd {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {n : ℕ} (hn : 0 < n) (a : D.La) (h : ∀ b, (n : ℤ) ∣ D.EF a b) : ∃ e, a = n • e := by
  choose c hc using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  let ψ : D.La →+ ℤ := AddMonoidHom.mk' c fun x y => mul_left_cancel₀ hn' (by rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)])
  obtain ⟨e, he⟩ := D.unimod.2 ψ.toIntLinearMap
  refine ⟨e, D.unimod.1 (LinearMap.ext fun b => ?_)⟩
  rw [map_nsmul, he, hc, LinearMap.smul_apply, nsmul_eq_mul]
  rfl

theorem exists_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type}
    [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  intro E _ _ _ H D X _ _ y n N hn hNn hC Z Z' hO σ w hσZ hσb hσy hσN hw hsat
  have hN : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  obtain ⟨k, hk⟩ := hNn
  have hnZ : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'

  have ha : ∀ z ∈ Z, ∃ e ∈ perp D Z', w z = z + N • e := by
    intro z hz
    obtain ⟨e, he⟩ := exists_eq_nsmul_of_forall_ef_dvd D hN (w z - z) fun b => by
      obtain ⟨b', hb', e, he⟩ := hσN b
      have h0 : D.EF z b' = 0 := by rw [ef_swap, hb' z hz, neg_zero]
      refine ⟨D.EF z e, ?_⟩
      simp only [map_sub, LinearMap.sub_apply, hw, he, map_add (f := _), map_nsmul, h0, nsmul_eq_mul]
      ring
    refine ⟨e, mem_perp.2 fun b hb => ?_, (sub_eq_iff_eq_add'.1 he)⟩
    have h1 : D.EF (w z - z) b = 0 := by rw [map_sub, LinearMap.sub_apply, hw, hσb b hb, sub_self]
    rw [he, map_nsmul, LinearMap.smul_apply, smul_eq_zero] at h1
    exact h1.resolve_left hN.ne'

  have hb : ∀ z a : D.La, (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (w z) a := by
    rintro z a ⟨e, he⟩
    obtain ⟨e₁, he₁⟩ := hσy a
    obtain ⟨e', -, he'⟩ := hsat (σ a) (hσZ a) ⟨e + e₁, by rw [he₁, he, smul_add]⟩
    refine ⟨D.EF z e', ?_⟩
    rw [hw, he', map_nsmul, nsmul_eq_mul]
  have hwy : ∀ z, ∃ e, y (w z) = n • e := fun z => hC.2 (w z) fun b hb' => hb z b hb'
  have hww : ∀ z z', (n : ℤ) ∣ D.EF (w z) (w z') := fun z z' => hb z (w z') (hwy z')
  obtain ⟨f, hf⟩ : ∃ f : Z → Z → ℤ, ∀ z z', (n : ℤ) * f z z' = D.EF (w z) (w z') :=
    ⟨fun z z' => D.EF (w z) (w z') / n, fun z z' => Int.mul_ediv_cancel' (hww _ _)⟩
  obtain ⟨β, hβ⟩ : ∃ β : LinearMap.BilinForm ℤ Z, ∀ a b, β a b = f a b :=
    ⟨LinearMap.mk₂ ℤ f
      (fun z₁ z₂ z' => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp))
      (fun z z₁ z₂ => mul_left_cancel₀ hnZ (by rw [mul_add, hf, hf, hf]; simp))
      (fun c z z' => mul_left_cancel₀ hnZ (by rw [smul_eq_mul, mul_left_comm, hf, hf]; simp)),
      fun _ _ => rfl⟩
  have hskew : ∀ a b, β a b = -β b a := fun a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [mul_neg, hf, hf, ef_swap])
  have hadj : ∀ (c : 𝓞 E) a b, β (c • a) b = β a (H.bar c • b) := fun c a b => by
    rw [hβ, hβ]
    exact mul_left_cancel₀ hnZ (by rw [hf, hf, Submodule.coe_smul, Submodule.coe_smul, w.map_smul, w.map_smul, D.adj])
  obtain ⟨c, hc⟩ := exists_skew_solve hO.2.2.1 β hskew hadj
  have ht : ∀ z : Z, (w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c)) z = w z - n • (c z : D.La) := fun z => rfl
  refine ⟨w ∘ₗ Z.subtype - n • (Z'.subtype ∘ₗ c), fun z => ?_, fun z z' => ?_, fun z a ha' => ?_⟩
  · obtain ⟨e₁, he₁, hwz⟩ := ha z z.2
    refine ⟨e₁ - k • (c z : D.La), sub_mem he₁ (nsmul_mem (hO.2.1 (c z).2) k), ?_⟩
    rw [ht, hwz, hk, smul_sub, mul_smul]
    abel
  · have e1 : D.EF (w z) (c z') = D.EF z (c z') := by rw [hw, hσb _ (c z').2]
    have e2 : D.EF (c z) (w z') = D.EF (c z) z' := by rw [ef_swap, hw, hσb _ (c z).2, ← ef_swap]
    have e3 : D.EF (c z) (c z') = 0 := hO.2.1 (c z).2 _ (c z').2
    have e4 : (n : ℤ) * β z z' = D.EF (w z) (w z') := by rw [hβ, hf]
    have e5 := hc z z'
    rw [ht, ht]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul, e1, e2, e3]
    linear_combination (-1 : ℤ) * e4 - (n : ℤ) * e5
  · rw [ht, map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_sub (hb z a ha') (dvd_mul_right _ _)

end GlobalTheory.LowFilt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjointStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isotropic_shear_of_adjoint : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    ∀ σ w : D.La →ₗ[𝓞 E] D.La, (∀ a, σ a ∈ Z') → (∀ b ∈ Z', σ b = b) → (∀ a, ∃ e, y (σ a) = y a + n • e) →
    (∀ a, ∃ b ∈ perp D Z, ∃ e, σ a = a + b + N • e) → (∀ a b, D.EF (w a) b = D.EF a (σ b)) →
    (∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e) →
    ∃ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) ∧ (∀ z z' : Z, D.EF (t z) (t z') = 0) ∧
      ∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a := by
  first | exact @GlobalTheory.LowFilt.exists_shear_of_adjoint | exact GlobalTheory.LowFilt.exists_shear_of_adjoint | (intros; apply GlobalTheory.LowFilt.exists_shear_of_adjoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicMod
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := GlobalTheory.T.injective_mod_of_surjective_mod_opposite D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := GlobalTheory.T.exists_linear_section_opposite_congr_mod D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := GlobalTheory.T.exists_isotropic_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add (f := _), map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add (f := _), map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicModStatement
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isometry_kernel_coisotropic_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_isometry_kerIs | exact GlobalTheory.LowFilt.exists_isometry_kerIs | (intros; apply GlobalTheory.LowFilt.exists_isometry_kerIs <;> assumption)
end
end
