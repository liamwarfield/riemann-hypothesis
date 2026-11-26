module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.StdHSingleZero

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.Imports
noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

theorem stepC : StepC := by
  intro a b c d ha hd lam hlam hok m _ _ Λa g hθ l hl hiso h1 hl1 h2
  classical
  set θ := cmTheta b d with hθdef
  set S := stdLat (cmL a b d ha hd lam hlam) m with hSdef
  set X := imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa with hXdef
  have hθn : θ * ((b : ℂ) - θ) = (a : ℂ) * c := theta_norm hok.1
  have hθθ : θ * θ = (b : ℂ) * θ - (a : ℂ) * c := by linear_combination -hθn

  have hXθ : ∀ x ∈ X, θ • x ∈ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨θ • y, hθ y hy, by simp⟩
  have hlin : ∀ p q : ℤ, ∀ x ∈ X, ((p : ℂ) + (q : ℂ) * θ) • x ∈ X := by
    intro p q x hx
    rw [add_smul, mul_smul, Int.cast_smul_eq_zsmul ℂ p, Int.cast_smul_eq_zsmul ℂ q]
    exact X.add_mem (X.zsmul_mem hx p) (X.zsmul_mem (hXθ x hx) q)

  obtain ⟨β, hβ⟩ : ∃ β : ℕ → ℂ, ∀ u, β u = 1 + ((u * l : ℕ) : ℂ) * θ := ⟨_, fun _ => rfl⟩
  obtain ⟨βb, hβb⟩ : ∃ βb : ℕ → ℂ, ∀ u, βb u = 1 + ((u * l : ℕ) : ℂ) * ((b : ℂ) - θ) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ → ℤ, ∀ u, K u = 1 + ((u * l : ℕ) : ℤ) * b + ((u * l : ℕ) : ℤ) ^ 2 * a * c :=
    ⟨_, fun _ => rfl⟩
  have hconj : ∀ u, (starRingEnd ℂ) (β u) = βb u := by
    intro u
    rw [hβ, hβb, map_add (f := _), map_one, map_mul, map_natCast, hθdef, theta_conj]
  have hK : ∀ u, β u * βb u = ((K u : ℤ) : ℂ) := by
    intro u
    rw [hβ, hβb, hKdef]
    push_cast
    linear_combination ((u : ℂ) * l) ^ 2 * hθn
  have hKpos : ∀ u, 0 < K u := by
    intro u
    rw [hKdef]
    set U : ℤ := ((u * l : ℕ) : ℤ) with hU
    have h4 := hok.1
    have hd1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
    have key : 4 * (1 + U * b + U ^ 2 * a * c) = (2 + U * b) ^ 2 + U ^ 2 * d := by
      linear_combination U ^ 2 * h4
    rcases eq_or_ne U 0 with h0 | h0
    · rw [h0]
      norm_num
    · have hU2 : 1 ≤ U ^ 2 := by
        have := pow_pos (abs_pos.2 h0) 2
        rw [sq_abs] at this
        omega
      nlinarith [sq_nonneg (2 + U * b)]
  have hβ0 : ∀ u, β u ≠ 0 := fun u h => by
    have := hK u
    rw [h, zero_mul] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)
  have hβb0 : ∀ u, βb u ≠ 0 := fun u h => by
    have := hK u
    rw [h, mul_zero] at this
    exact (hKpos u).ne' (by exact_mod_cast this.symm)

  have hinj : Function.Injective (fun u => (β u / βb u)⁻¹) := by
    intro u v huv
    simp only [inv_inj] at huv
    rw [div_eq_div_iff (hβb0 u) (hβb0 v), hβ, hβ, hβb, hβb] at huv
    have h2θ : 2 * θ - b ≠ 0 := two_theta_sub b hd
    have hmul : (((u * l : ℕ) : ℂ) - ((v * l : ℕ) : ℂ)) * (2 * θ - b) = 0 := by
      linear_combination huv
    rcases mul_eq_zero.1 hmul with h | h
    · have h' : u * l = v * l := Nat.cast_injective (sub_eq_zero.1 h)
      exact Nat.eq_of_mul_eq_mul_right hl.pos h'
    · exact absurd h h2θ

  have hfin := Module.End.finite_hasEigenvalue (g : Module.End ℂ (m → ℂ))
  obtain ⟨_, ⟨u, rfl⟩, hu⟩ := (Set.infinite_range_of_injective hinj).exists_notMem_finite hfin
  set w := β u / βb u with hwdef
  have hw0 : w ≠ 0 := div_ne_zero (hβ0 u) (hβb0 u)
  let δ : (m → ℂ) ≃ₗ[ℂ] (m → ℂ) := g.trans (LinearEquiv.smulOfNeZero ℂ (m → ℂ) w hw0)
  have hδ : ∀ x, δ x = w • g x := fun x => rfl
  have hcb : (starRingEnd ℂ) (βb u) = β u := by rw [← hconj u, Complex.conj_conj]
  have hww : (starRingEnd ℂ) w * w = 1 := by
    rw [hwdef, map_div₀, hconj u, hcb]
    field_simp [hβ0 u, hβb0 u]
  have hisoδ : IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m)
      (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) := by
    intro x y
    show stdH (cmL a b d ha hd lam hlam) m (w • g x) (w • g y) = stdH (cmL a b d ha hd lam hlam) m x y
    rw [LinearMap.map_smul (stdH (cmL a b d ha hd lam hlam) m) w (g x), LinearMap.smul_apply,
      LinearMap.map_smulₛₗ, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm w, hww, one_mul]
    exact hiso x y
  have himg : imgLat (δ : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa = X.map (smulHom w) := by
    rw [hXdef]
    unfold imgLat
    rw [AddSubgroup.map_map]
    congr 1

  set Nn := (K u).toNat with hNndef
  have hNnZ : ((Nn : ℕ) : ℤ) = K u := Int.toNat_of_nonneg (hKpos u).le
  have hNn : ((Nn : ℕ) : ℂ) = β u * βb u := by
    rw [hK u, ← hNnZ, Int.cast_natCast]
  have hN0 : Nn ≠ 0 := by have := hKpos u; omega
  have ha' : ∀ x ∈ X, (Nn : ℂ) • w • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w = (((1 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        (((2 * ((u * l : ℕ) : ℤ) + ((u * l : ℕ) : ℤ) ^ 2 * b : ℤ)) : ℂ) * θ := by
      rw [hNn, hwdef]
      have : β u * βb u * (β u / βb u) = β u * β u := by field_simp [hβb0 u]
      rw [this, hβ]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  have hb' : ∀ x ∈ X, (Nn : ℂ) • w⁻¹ • x ∈ X := by
    intro x hx
    have heq : (Nn : ℂ) * w⁻¹ = ((((1 + ((u * l : ℕ) : ℤ) * b) ^ 2 - ((u * l : ℕ) : ℤ) ^ 2 * a * c : ℤ)) : ℂ) +
        ((((u * l : ℕ) : ℤ) ^ 2 * b - 2 * (1 + ((u * l : ℕ) : ℤ) * b) * ((u * l : ℕ) : ℤ) : ℤ) : ℂ) * θ := by
      rw [hNn, hwdef, inv_div]
      have : β u * βb u * (βb u / β u) = βb u * βb u := by field_simp [hβ0 u]
      rw [this, hβb]
      push_cast
      linear_combination ((u : ℂ) * l) ^ 2 * hθθ
    rw [smul_smul, heq]
    exact hlin _ _ x hx
  obtain ⟨hi1, hi2⟩ := comm_smul (S := S) (X := X) hw0 hN0 (stdLat_smul_idx _ m hN0) h1 h2 ha' hb'

  have hM : ∀ x ∈ X, (S.relIndex X) • x ∈ S := by
    intro x hx
    have := AddSubgroup.nsmul_index_mem (S.addSubgroupOf X) ⟨x, hx⟩
    rw [AddSubgroup.mem_addSubgroupOf] at this
    simpa [AddSubgroup.relIndex] using this
  have hNl : ¬ l ∣ Nn := by
    intro hdiv
    have h1' : (l : ℤ) ∣ K u := by
      have := Int.natCast_dvd_natCast.2 hdiv
      rwa [hNnZ] at this
    have h2' : (l : ℤ) ∣ K u - 1 :=
      ⟨(u : ℤ) * (b + ((u * l : ℕ) : ℤ) * a * c), by rw [hKdef]; push_cast; ring⟩
    have h3 : (l : ℤ) ∣ 1 := by
      have := Int.dvd_sub h1' h2'
      simpa using this
    have h4 : (l : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) h3
    exact hl.one_lt.ne' (by exact_mod_cast h4)
  have hln : ¬ l ∣ S.relIndex X * Nn := fun h => ((Nat.Prime.dvd_mul hl).1 h).elim hl1 hNl
  have hdvd := not_dvd_relIndex (A := S) (B := X.map (smulHom w)) (l := l) (n := S.relIndex X * Nn) hl hi1
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [smulHom_apply, mul_smul, ← Nat.cast_smul_eq_nsmul ℂ Nn]
      exact hM _ (ha' x hx)) hln
  refine ⟨δ, hisoδ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    by_contra hx0
    apply hu
    have hgx : (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • x := by
      rw [hδ] at hx
      calc (g : Module.End ℂ (m → ℂ)) x = w⁻¹ • (w • g x) := by rw [inv_smul_smul₀ hw0]; rfl
        _ = w⁻¹ • x := by rw [hx]
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x) ?_
    first
      | exact Module.End.hasEigenvector_iff.2 ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
      | exact ⟨Module.End.mem_eigenspace_iff.2 hgx, hx0⟩
  · unfold relIdx
    rw [himg]
    exact hi1
  · unfold relIdx
    rw [himg]
    exact hdvd
  · unfold relIdx
    rw [himg]
    exact hi2

end PI.UnitaryGroupMassFormula.UnimodLocStd
end
end

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

variable {a : ℕ} {b c : ℤ} {d : ℕ} {ha : 0 < a} {hd : 0 < d} {lam : ℂ} {hlam : lam ≠ 0}

lemma isKv_of_sat {m : Type*} [Fintype m] [DecidableEq m] {l : ℕ} (hl : l.Prime) {Λ : AddSubgroup (m → ℂ)}
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λ ≠ 0) {v : m → ℂ} (hv : SatMem l Λ v) :
    IsKv b d lam v := by
  obtain ⟨n, hln, hn⟩ := hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hln (dvd_zero l)
  set S := stdLat (cmL a b d ha hd lam hlam) m
  have hmem : (S.addSubgroupOf Λ).index • (⟨n • v, hn⟩ : Λ) ∈ S.addSubgroupOf Λ :=
    AddSubgroup.nsmul_index_mem _ _
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_nsmul, smul_smul] at hmem
  have hN : (S.addSubgroupOf Λ).index * n ≠ 0 := mul_ne_zero h1 hn0
  exact isKv_of_nsmul hN (isKv_of_mem hmem)

lemma exists_isometry_memLocalizedAt_single (hkey : KeyRep) (hok : CmOK a b c d) (m : Type) [Fintype m] [DecidableEq m]
    (Λa : AddSubgroup (m → ℂ)) (hsd : IsSelfDual (stdH (cmL a b d ha hd lam hlam) m) Λa)
    (hθ : ∀ x ∈ Λa, cmTheta b d • x ∈ Λa)
    (h1 : relIdx (stdLat (cmL a b d ha hd lam hlam) m) Λa ≠ 0)
    (h2 : relIdx Λa (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0)
    {l : ℕ} (hl : l.Prime) (x y : ℤ) (hQ : ¬ (l : ℤ) ∣ a * x ^ 2 + b * x * y + c * y ^ 2) (T : Finset m) :
    ∃ g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ),
      IsIsom (stdH (cmL a b d ha hd lam hlam) m) (stdH (cmL a b d ha hd lam hlam) m) (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) ∧
      relIdx (stdLat (cmL a b d ha hd lam hlam) m) (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) ≠ 0 ∧
      relIdx (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) (stdLat (cmL a b d ha hd lam hlam) m)) (stdLat (cmL a b d ha hd lam hlam) m) ≠ 0 ∧
      ∀ j ∈ T, SatMem l (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa) (Pi.single j (lam * ((x * a : ℂ) + y * cmTheta b d))) := by
  classical
  have himg : ∀ (g : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) (Λ : AddSubgroup (m → ℂ)), (∀ z ∈ Λ, cmTheta b d • z ∈ Λ) →
      ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ := by
    intro g Λ hΛ z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λ z).1 hz
    exact (mem_imgLat_iff g Λ _).2 ⟨_, hΛ w hw, map_smul g _ w⟩
  have hαK : (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam = (x * a : ℂ) + y * cmTheta b d := by
    field_simp
  have hα0 : lam * ((x * a : ℂ) + y * cmTheta b d) ≠ 0 := by
    intro h0
    rw [alpha_eq (ha := ha) (hd := hd) (hlam := hlam)] at h0
    obtain ⟨hx0, hy0⟩ := LinearIndependent.pair_iff.1 (cmL a b d ha hd lam hlam).indep _ _ h0
    have hx : x = 0 := by exact_mod_cast hx0
    have hy : y = 0 := by exact_mod_cast hy0
    apply hQ
    simp [hx, hy]
  induction T using Finset.induction_on with
  | empty =>
    have hid : ∀ Λ : AddSubgroup (m → ℂ),
        imgLat ((LinearEquiv.refl ℂ (m → ℂ) : (m → ℂ) ≃ₗ[ℂ] (m → ℂ)) : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λ = Λ := by
      intro Λ
      ext z
      rw [mem_imgLat_iff]
      simp
    refine ⟨LinearEquiv.refl ℂ (m → ℂ), fun _ _ => rfl, ?_, ?_, by simp⟩
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
    · rw [hid, relIdx, AddSubgroup.relIndex_self]
      exact one_ne_zero
  | insert i₀ T hi₀ ih =>
    obtain ⟨g, hgI, hg1, hg2, hgT⟩ := ih
    have hc := comm_img g hg1 hg2 h1 h2
    have hsd' := selfDual_img _ g hgI hsd
    have hθ' := himg g Λa hθ
    obtain ⟨v, hvS, hvT, hvv⟩ := hkey a b c d ha hd lam hlam hok m _ hsd' hθ' hc.1 hc.2 l hl x y hQ T i₀ hi₀ hgT
    have hvK : IsKv b d lam v := isKv_of_sat hl hc.1 hvS
    have hK : ∀ s : ℂ, s = 1 ∨ s = -1 →
        IsK b d (s * (lam * ((x * a : ℂ) + y * cmTheta b d)) / lam) := by
      intro s hs
      have hb : IsK b d ((x * a : ℂ) + y * cmTheta b d) :=
        ⟨x * a, y, 1, one_ne_zero, by push_cast; ring⟩
      rcases hs with rfl | rfl
      · rw [one_mul, hαK]
        exact hb
      · rw [neg_one_mul, neg_div, hαK]
        exact isK_neg hb
    have hee : stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d)))
        (Pi.single i₀ (lam * ((x * a : ℂ) + y * cmTheta b d))) ≠ 0 := by
      rw [stdH_kappa _ hlam, Finset.sum_eq_single i₀ (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
        (fun h => absurd (Finset.mem_univ i₀) h), Pi.single_eq_same]
      exact mul_ne_zero (kappa_ne _ hlam)
        (mul_ne_zero (div_ne_zero hα0 hlam) ((map_ne_zero _).2 (div_ne_zero hα0 hlam)))
    obtain ⟨s, hs, hne⟩ : ∃ s : ℂ, (s = 1 ∨ s = -1) ∧
        stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) ≠ 0 := by
      by_cases h : stdH (cmL a b d ha hd lam hlam) m v v - stdH (cmL a b d ha hd lam hlam) m v
          (Pi.single i₀ (1 * (lam * ((x * a : ℂ) + y * cmTheta b d)))) = 0
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, Pi.single_neg, map_neg]
        rw [one_mul, sub_eq_zero] at h
        rw [sub_neg_eq_add, ← h, ← two_mul, hvv]
        exact mul_ne_zero two_ne_zero hee
      · exact ⟨1, Or.inl rfl, h⟩
    have hss : s * s = 1 := by
      rcases hs with rfl | rfl <;> norm_num
    have hvv' : stdH (cmL a b d ha hd lam hlam) m v v =
        stdH (cmL a b d ha hd lam hlam) m (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d))))
          (Pi.single i₀ (s * (lam * ((x * a : ℂ) + y * cmTheta b d)))) := by
      rw [hvv]
      rcases hs with rfl | rfl
      · simp only [one_mul]
      · simp only [neg_one_mul, Pi.single_neg, map_neg, LinearMap.neg_apply, neg_neg]
    obtain ⟨σ, hσI, hσ1, hσ2, hσv, hσfix⟩ :=
      qrefl_to hok v _ hvv' hne hvK (isKv_single (hK s hs) i₀)
    refine ⟨g.trans σ, isom_trans _ g σ hgI hσI, ?_, ?_, ?_⟩
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).1
    · rw [imgLat_trans]
      exact (comm_img σ hσ1 hσ2 hg1 hg2).2
    · intro j hj
      rw [imgLat_trans]
      rcases Finset.mem_insert.1 hj with rfl | hjT
      · obtain ⟨n, hln, hn⟩ := hvS
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨s • n • v, ?_, ?_⟩⟩
        · rcases hs with rfl | rfl
          · rwa [one_smul]
          · rw [neg_one_smul]
            exact AddSubgroup.neg_mem _ hn
        · rw [map_smul, map_nsmul, hσv, smul_comm, ← Pi.single_smul', smul_eq_mul, ← mul_assoc, hss, one_mul]
      · obtain ⟨n, hln, hn⟩ := hgT j hjT
        refine ⟨n, hln, (mem_imgLat_iff σ _ _).2 ⟨_, hn, ?_⟩⟩
        rw [map_nsmul, hσfix]
        apply stdH_single_zero
        have hne' : j ≠ i₀ := fun h => hi₀ (h ▸ hjT)
        simp [hvT j hjT, Pi.single_eq_of_ne hne']

theorem stepB_of_key (hkey : KeyRep) : StepB := by
  intro a b c d ha hd lam hlam hok m _ _ Λa hsd hθ h1 h2 l hl
  obtain ⟨x, y, hQ⟩ := exists_good_form hok hl
  obtain ⟨g, hgI, hg1, hg2, hgT⟩ := exists_isometry_memLocalizedAt_single hkey hok m Λa hsd hθ h1 h2 hl x y hQ Finset.univ
  have hc := comm_img g hg1 hg2 h1 h2
  have hsd' := selfDual_img _ g hgI hsd
  have hθ' : ∀ z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa, cmTheta b d • z ∈ imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := (mem_imgLat_iff g Λa z).1 hz
    exact (mem_imgLat_iff g Λa _).2 ⟨_, hθ w hw, map_smul g _ w⟩
  obtain ⟨n, hln, hn⟩ := sat_std_of_all hok hl x y hQ _ hsd' hθ' (fun j => hgT j (Finset.mem_univ j))
  refine ⟨g, hgI, hc.1, ?_, hc.2⟩
  intro hdvd
  have hfi : ((stdLat (cmL a b d ha hd lam hlam) m).addSubgroupOf
      (imgLat (g : (m → ℂ) →ₗ[ℂ] (m → ℂ)) Λa)).FiniteIndex := ⟨hc.1⟩
  have : Fact l.Prime := ⟨hl⟩
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card' l hdvd
  have hnq : n • q = 0 := by
    induction q using QuotientAddGroup.induction_on with
    | H w =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
        AddSubgroup.coe_nsmul]
      exact hn w w.2
  have h := addOrderOf_dvd_of_nsmul_eq_zero hnq
  rw [hq] at h
  exact hln h

theorem target_of_key (hkey : KeyRep) : PI.UnimodLocStd := target_of (stepB_of_key hkey) stepC

end PI.UnitaryGroupMassFormula.UnimodLocStd
