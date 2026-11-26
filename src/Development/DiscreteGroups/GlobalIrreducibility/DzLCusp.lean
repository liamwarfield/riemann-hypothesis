module

public import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
public import Development.DiscreteGroups.GlobalIrreducibility.DzLcIso
public import Development.DiscreteGroups.GlobalIrreducibility.DzTypeCut

@[expose] public section

section -- merged from Development.DiscreteGroups.GlobalIrreducibility.DzLcPerm
noncomputable section

open Matrix

namespace DiscreteGroups.sglob.DzLc

variable {F : Type} [Field F] {N : ℕ}

theorem strict_left_mul {b : Fin N → ℕ} {X Y : Matrix (Fin N) (Fin N) F}
    (hX : X.BlockTriangular b) (hY : GlobalTheory.FiniteGL.IsStrictBlock b Y) : GlobalTheory.FiniteGL.IsStrictBlock b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_or_ge (b l) (b i) with h | h
  · rw [hX h, zero_mul]
  · rw [hY l j (le_trans hij h), mul_zero]

theorem conj_mem_unipRadical {b : Fin N → ℕ} {p u : GL (Fin N) F}
    (hp : (p : Matrix (Fin N) (Fin N) F).BlockTriangular b) (hu : u ∈ GlobalTheory.FiniteGL.unipRadical F b) :
    p * u * p⁻¹ ∈ GlobalTheory.FiniteGL.unipRadical F b := by
  have hpi : ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F).BlockTriangular b := by
    let _ := p.invertible
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hp
  have h1 : (p : Matrix (Fin N) (Fin N) F) * ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have e : ((p * u * p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) - 1 =
      (p : Matrix (Fin N) (Fin N) F) * ((u : Matrix (Fin N) (Fin N) F) - 1) *
        ((p⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, h1]
  refine GlobalTheory.FiniteGL.mem_unipRadical.2 fun i j hij => ?_
  rw [e, Matrix.mul_assoc]
  exact strict_left_mul hp
    (GlobalTheory.FiniteGL.IsStrictBlock.mul_blockTriangular (GlobalTheory.FiniteGL.mem_unipRadical.1 hu) hpi) i j hij

theorem monotone_twoBlocks (a : ℕ) : Monotone (GlobalTheory.FiniteGL.twoBlocks N a) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [GlobalTheory.FiniteGL.twoBlocks]
  split_ifs <;> omega

theorem blockUpper_le_normalizer (b : Fin N → ℕ) :
    GroundTheory.Automorphic.Iwasawa.blockUpper F N b ≤
      Subgroup.normalizer (GlobalTheory.FiniteGL.unipRadical F b : Set (GL (Fin N) F)) := by
  intro p hp
  refine Subgroup.mem_normalizer_iff.2 fun u => ⟨fun hu => conj_mem_unipRadical hp hu, fun hu => ?_⟩
  have hp' : p⁻¹ ∈ GroundTheory.Automorphic.Iwasawa.blockUpper F N b := inv_mem hp
  have := conj_mem_unipRadical hp' hu
  have e : p⁻¹ * (p * u * p⁻¹) * p⁻¹⁻¹ = u := by group
  rwa [e] at this

theorem exists_cut (f : Fin N → ℕ) (hf : Monotone f) (h : ∃ x y, f x ≠ f y) :
    ∃ a, 0 < a ∧ a < N ∧ ∀ i j : Fin N, (i : ℕ) < a → a ≤ (j : ℕ) → f i < f j := by
  classical
  obtain ⟨x, y, hxy⟩ := h
  have hN : 0 < N := x.pos
  have hex : ∃ m, ∃ hm : m < N, f ⟨m, hm⟩ ≠ f ⟨0, hN⟩ := by
    by_contra hcon
    push Not at hcon
    exact hxy ((hcon x x.2).trans (hcon y y.2).symm)
  obtain ⟨hm, hne⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, ?_, hm, fun i j hi hj => ?_⟩
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | h0
    · exact absurd (congrArg f (Fin.ext h0 : (⟨Nat.find hex, hm⟩ : Fin N) = ⟨0, hN⟩)) hne
    · exact h0
  · have h1 : f i = f ⟨0, hN⟩ := by
      by_contra hc
      exact Nat.find_min hex hi ⟨i.2, hc⟩
    have h2 : f ⟨Nat.find hex, hm⟩ ≤ f j := hf (show (⟨Nat.find hex, hm⟩ : Fin N) ≤ j from hj)
    have h3 : f ⟨0, hN⟩ ≤ f ⟨Nat.find hex, hm⟩ :=
      hf (show (⟨0, hN⟩ : Fin N) ≤ ⟨Nat.find hex, hm⟩ from Nat.zero_le _)
    rw [h1]
    exact lt_of_lt_of_le (lt_of_le_of_ne h3 (Ne.symm hne)) h2

theorem exists_perm_conj {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    (he : GlobalTheory.SmGL.unipRad F e ≠ ⊥) :
    ∃ (Q : GL (Fin N) F) (a : ℕ), 0 < a ∧ a < N ∧
      ∀ x ∈ GlobalTheory.FiniteGL.unipRadical F (GlobalTheory.FiniteGL.twoBlocks N a), Q * x * Q⁻¹ ∈ GlobalTheory.SmGL.unipRad F e := by
  classical
  obtain ⟨β, hβ⟩ : ∃ β : Fin N → ℕ, β = fun x => ((GlobalTheory.SmGL.blk e x : Fin s) : ℕ) := ⟨_, rfl⟩
  have hβe : ∀ c (i : Fin (d c)), β (e ⟨c, i⟩) = c := fun c i => by subst hβ; simp
  obtain ⟨x0, y0, hxy⟩ : ∃ x y, β x ≠ β y := by
    by_contra hcon
    push Not at hcon
    apply he
    refine (Subgroup.eq_bot_iff_forall _).2 fun u hu => ?_
    obtain ⟨-, hdiag⟩ := GlobalTheory.SmGL.mem_unipRad.1 hu
    refine Matrix.GeneralLinearGroup.ext fun x y => ?_
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective x
    obtain ⟨⟨c', j⟩, rfl⟩ := e.surjective y
    have hcc : c = c' := by
      have := hcon (e ⟨c, i⟩) (e ⟨c', j⟩)
      rw [hβe, hβe] at this
      exact Fin.ext this
    subst hcc
    rw [hdiag c i j]
    simp [Matrix.one_apply, e.injective.eq_iff]
  obtain ⟨ν, hν⟩ : ∃ ν : Equiv.Perm (Fin N), ν = Tuple.sort β := ⟨_, rfl⟩
  have hmono : Monotone (β ∘ ν) := hν ▸ Tuple.monotone_sort β
  obtain ⟨a, ha0, haN, hcut⟩ := exists_cut (β ∘ ν) hmono
    ⟨ν.symm x0, ν.symm y0, by simpa using hxy⟩
  have h12 : (ν.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * ν.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext u v
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  have h21 : (ν.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * ν.symm.toPEquiv.toMatrix = 1 := by
    rw [PEquiv.toMatrix_toPEquiv_mul]
    ext u v
    simp [PEquiv.toMatrix_apply, Matrix.one_apply]
  let Q : GL (Fin N) F := ⟨_, _, h12, h21⟩
  have hQ : ∀ X : GL (Fin N) F, ∀ u v, ((Q * X * Q⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) u v =
      (X : Matrix (Fin N) (Fin N) F) (ν.symm u) (ν.symm v) := by
    intro X u v
    show (((ν.symm.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F) * (X : Matrix (Fin N) (Fin N) F) *
      ν.toPEquiv.toMatrix : Matrix (Fin N) (Fin N) F)) u v = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    simp
  refine ⟨Q, a, ha0, haN, fun x hx => ?_⟩
  have hxe := GlobalTheory.FiniteGL.mem_unipRadical.1 hx
  have key : ∀ p q : Fin N, (x : Matrix (Fin N) (Fin N) F) p q ≠ (1 : Matrix (Fin N) (Fin N) F) p q →
      β (ν p) < β (ν q) := by
    intro p q hpq
    by_cases hp : (p : ℕ) < a
    · by_cases hq : a ≤ (q : ℕ)
      · exact hcut p q hp hq
      · exfalso
        apply hpq
        have h := hxe p q (by unfold GlobalTheory.FiniteGL.twoBlocks; split_ifs <;> omega)
        rw [Matrix.sub_apply, sub_eq_zero] at h
        exact h
    · exfalso
      apply hpq
      have h := hxe p q (by unfold GlobalTheory.FiniteGL.twoBlocks; split_ifs <;> omega)
      rw [Matrix.sub_apply, sub_eq_zero] at h
      exact h
  refine GlobalTheory.SmGL.mem_unipRad.2 ⟨GlobalTheory.SmGL.mem_parab.2 fun u v huv => ?_, fun c i j => ?_⟩
  · rw [hQ x u v]
    have hne : u ≠ v := fun h => by subst h; exact lt_irrefl _ huv
    have h1 : (1 : Matrix (Fin N) (Fin N) F) (ν.symm u) (ν.symm v) = 0 :=
      Matrix.one_apply_ne fun h => hne (ν.symm.injective h)
    by_contra hc
    have h2 := key (ν.symm u) (ν.symm v) (by rw [h1]; exact hc)
    simp only [Equiv.apply_symm_apply] at h2
    have h3 : β v < β u := by rw [hβ]; exact huv
    exact lt_asymm h2 h3
  · rw [hQ x]
    by_cases hij : i = j
    · subst hij
      have h := hxe (ν.symm (e ⟨c, i⟩)) (ν.symm (e ⟨c, i⟩)) le_rfl
      rw [Matrix.sub_apply, sub_eq_zero, Matrix.one_apply_eq] at h
      rw [h, Matrix.one_apply_eq]
    · have hne : e ⟨c, i⟩ ≠ e ⟨c, j⟩ := fun h => hij (by simpa using e.injective h)
      rw [Matrix.one_apply_ne hij]
      by_contra hc
      have h2 := key _ _ (by rwa [Matrix.one_apply_ne (fun h => hne (ν.symm.injective h))])
      simp only [Equiv.apply_symm_apply] at h2
      rw [hβe, hβe] at h2
      exact lt_irrefl _ h2

end DiscreteGroups.sglob.DzLc
end
end

noncomputable section

open GlobalTheory.GLq GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LocGL GlobalTheory.LocLanglands
open scoped Classical

namespace DiscreteGroups.sglob.DzLc

variable {g : ℕ} [Fact g.Prime] {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]

theorem twKer_twoBlocks_eq_top (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n a : ℕ} (h0 : 0 < a) (ha : a < n)
    (τ : FDRep ℂ (Gn g n)) (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 = ⊤ := by
  obtain ⟨φ, hφ0, hφ⟩ := hs
  have hgen : ∀ x : GL (Fin n) k, x ∈ GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a) → ∀ v,
      σ.ρ x v - v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro x hx v
    refine Submodule.subset_span ⟨⟨x, hx⟩, v, ?_⟩
    simp
  have hφT : ∀ w, φ w ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro w
    have hfin := sum_unip_eq_zero τ hτ h0 ha
    have key : ∀ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        φ w - φ (τ.ρ (u : Gn g n) w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
      intro u
      obtain ⟨κ, hred, hmem⟩ := exists_lift i (u : Gn g n) u.2
      have h1 := hφ κ w
      rw [hred] at h1
      rw [h1, ← neg_sub]
      exact Submodule.neg_mem _ (hgen _ hmem (φ w))
    have hsum : ∑ u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a),
        (φ w - φ (τ.ρ (u : Gn g n) w)) =
          (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) • φ w := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_sub_distrib, ← map_sum φ (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n) w),
        ← LinearMap.sum_apply Finset.univ
          (fun u : GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a) => τ.ρ (u : Gn g n)) w, hfin, LinearMap.zero_apply, map_zero,
        sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    have hc : (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 Fintype.card_ne_zero
    have hmem := Submodule.sum_mem _ fun u (_ : u ∈ Finset.univ) => key u
    rw [hsum] at hmem
    have := Submodule.smul_mem _
      (Fintype.card (GlobalTheory.FiniteGL.unipRadical (ZMod g) (GlobalTheory.FiniteGL.twoBlocks n a)) : ℂ)⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hall : ∀ (h : GL (Fin n) k) (w : τ),
      σ.ρ h (φ w) ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    intro h w
    obtain ⟨p, hp, k0, hk0, rfl⟩ :=
      GroundTheory.Automorphic.Iwasawa.exists_blockUpper_mul_integralGL k n (monotone_twoBlocks (N := n) a) h
    obtain ⟨κ, rfl⟩ := exists_inc_eq i hi k0 hk0
    rw [map_mul, Module.End.mul_apply]
    refine twKer_le_comap σ.ρ _ p (blockUpper_le_normalizer (GlobalTheory.FiniteGL.twoBlocks n a) hp) ?_
    have h1 := hφ κ w
    rw [show (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) (GlobalTheory.GLp.inc g n κ) (φ w) =
      σ.ρ (Matrix.GeneralLinearGroup.map i.toRingHom (GlobalTheory.GLp.inc g n κ)) (φ w) from rfl] at h1
    rw [← h1]
    exact hφT _
  obtain ⟨w0, hw0⟩ : ∃ w, φ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hφ0 (LinearMap.ext hcon)
  let S : Subrepresentation σ.ρ :=
    ⟨Submodule.span ℂ {v | ∃ (h : GL (Fin n) k) (w : τ), v = σ.ρ h (φ w)}, fun x v hv => by
      refine (Submodule.span_le.2 ?_ : _ ≤ (Submodule.span ℂ _).comap (σ.ρ x)) hv
      rintro _ ⟨h, w, rfl⟩
      exact Submodule.subset_span ⟨x * h, w, by rw [map_mul, Module.End.mul_apply]⟩⟩
  have hST : S.toSubmodule ≤ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 :=
    Submodule.span_le.2 (by rintro _ ⟨h, w, rfl⟩; exact hall h w)
  have hirr := σ.irr
  rcases eq_bot_or_eq_top S with hS | hS
  · exfalso
    have hm : φ w0 ∈ S.toSubmodule := Submodule.subset_span ⟨1, w0, by rw [map_one, Module.End.one_apply]⟩
    rw [hS] at hm
    exact hw0 ((Submodule.mem_bot ℂ).1 hm)
  · refine eq_top_iff.2 fun v _ => hST ?_
    rw [hS]
    trivial

theorem isCuspidal_of_inflates (i : ℚ_[g] ≃+* k) (hi : Continuous i) {n : ℕ} (τ : FDRep ℂ (Gn g n))
    (hτ : GlobalTheory.GLq.IsCusp τ.character) (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) k))
    (hs : GlobalTheory.SerSys.TameGen.Inflates (σ.ρ.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) τ) :
    IsCuspidal σ.ρ := by
  refine ⟨σ.smooth, fun s d e he => ?_⟩
  obtain ⟨Q, a, h0, ha, hQ⟩ := exists_perm_conj e he
  have htop := twKer_twoBlocks_eq_top i hi h0 ha τ hτ σ hs
  have hinvQ : ∀ z, σ.ρ Q⁻¹ (σ.ρ Q z) = z := fun z => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hmap : twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 ≤
      (twKer σ.ρ (unipRad k e) 1).comap (σ.ρ Q) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨x, hx⟩, y, rfl⟩
    refine Submodule.subset_span ⟨⟨Q * x * Q⁻¹, hQ x hx⟩, σ.ρ Q y, ?_⟩
    simp [map_mul, Module.End.mul_apply, hinvQ]
  refine Submodule.Quotient.subsingleton_iff.2 (eq_top_iff.2 fun v _ => ?_)
  have hv : σ.ρ Q⁻¹ v ∈ twKer σ.ρ (GlobalTheory.FiniteGL.unipRadical k (GlobalTheory.FiniteGL.twoBlocks n a)) 1 := by
    rw [htop]
    exact Submodule.mem_top
  have := hmap hv
  rwa [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] at this

end DiscreteGroups.sglob.DzLc

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end DiscreteGroups.sglob.DzType
