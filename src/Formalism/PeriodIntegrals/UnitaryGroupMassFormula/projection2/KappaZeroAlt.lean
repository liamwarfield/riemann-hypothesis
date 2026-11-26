module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.Assemble

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.GaStep
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.MemFlagUnipotent
noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

private theorem symm_mem_Ufl_of_maps_Ufl {i : ℕ} {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    (h : ∀ v ∈ PI.OneCosetSharp.Loc.Ufl k n c i, r v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) {v : Fin (n + c) → k}
    (hv : v ∈ PI.OneCosetSharp.Loc.Ufl k n c i) : r.symm v ∈ PI.OneCosetSharp.Loc.Ufl k n c i := by
  have hle : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) ≤ PI.OneCosetSharp.Loc.Ufl k n c i := by
    rintro _ ⟨w, hw, rfl⟩
    exact h w hw
  have heq : (PI.OneCosetSharp.Loc.Ufl k n c i).map (r : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k)) = PI.OneCosetSharp.Loc.Ufl k n c i :=
    Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq r _)
  rw [← heq] at hv
  obtain ⟨w, hw, hwv⟩ := hv
  have : r.symm v = w := by
    rw [LinearEquiv.symm_apply_eq]
    exact hwv.symm
  rw [this]
  exact hw

theorem R1cond_symm {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : R1cond k n c r.symm := by
  obtain ⟨h1, h2, h3⟩ := hr
  refine ⟨fun i v hv => symm_mem_Ufl_of_maps_Ufl (h1 i) hv, ?_, fun i => ?_⟩
  · rw [LinearEquiv.symm_apply_eq]
    exact h2.symm
  · have hu := symm_mem_Ufl_of_maps_Ufl (h1 i) (h3 i)
    have hneg := (PI.OneCosetSharp.Loc.Ufl k n c i).neg_mem hu
    have : r.symm (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i) =
        -r.symm (r (PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) - PI.OneCosetSharp.Loc.eN k (n + c) (n + i)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply, neg_sub]
    rw [this]
    exact hneg

theorem mem_flagUnipotent {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : r ∈ R1 k n c :=
  ⟨hr, R1cond_symm hr⟩

theorem mem_Ufl {i : ℕ} {v : Fin (n + c) → k} : v ∈ Ufl k n c i ↔ ∀ l : Fin (n + c), n + i ≤ l.1 → v l = 0 := by
  show (∀ l : Fin (n + c), l.1 ∉ {l | l < n + i} → v l = 0) ↔ _
  simp only [Set.mem_ofPred_eq, not_lt]

def XP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then LinearMap.proj l else 0

def AP : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k) :=
  LinearMap.pi fun l => if l.1 < n then 0 else LinearMap.proj l

theorem lowProj_apply₂ (v : Fin (n + c) → k) (l : Fin (n + c)) : (XP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then v l else 0 := by
  by_cases h : l.1 < n <;> simp [XP, h]

theorem projA_apply (v : Fin (n + c) → k) (l : Fin (n + c)) : (AP : (Fin (n + c) → k) →ₗ[k] _) v l = if l.1 < n then 0 else v l := by
  by_cases h : l.1 < n <;> simp [AP, h]

theorem lowProj_add_highProj (v : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) v + AP v = v := by
  funext l
  rw [Pi.add_apply, lowProj_apply₂, projA_apply]
  by_cases h : l.1 < n <;> simp [h]

theorem projA_inX (v : Fin n → k) : (AP : (Fin (n + c) → k) →ₗ[k] _) (inX k n c v) = 0 := by
  funext l
  rw [projA_apply]
  by_cases h : l.1 < n
  · simp [h]
  · simp [h, PI.OneCosetSharp.Loc.inX]

end PI.OneCosetSharp.W
end
end

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

theorem eN_apply (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl

theorem XP_AP (w : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) (AP w) = 0 := by
  funext l
  rw [lowProj_apply₂, projA_apply]
  split_ifs <;> rfl

theorem lowProj_basisVec_of_le (q : ℕ) (hq : n ≤ q) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = 0 := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

theorem lowProj_basisVec_of_lt (q : ℕ) (hq : q < n) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = eN k (n + c) q := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

theorem projA_eq_self_of_projX_eq_zero {w : Fin (n + c) → k} (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : AP w = w := by
  have h := lowProj_add_highProj (n := n) (c := c) w
  rwa [hw, zero_add] at h

theorem fix_of_basis (g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (hga : ∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) (w : Fin (n + c) → k)
    (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : g w = w := by
  have hsum : w = ∑ l : Fin (n + c), w l • PI.OneCosetSharp.Loc.eN k (n + c) l.1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp [eN_apply]
    · intro b _ hb
      have hx : x.1 ≠ b.1 := fun h => hb (Fin.ext h).symm
      simp [eN_apply, hx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul]
  by_cases hl : l.1 < n
  · have h0 : w l = 0 := by
      have h1 := congrFun hw l
      rw [lowProj_apply₂, if_pos hl] at h1
      exact h1
    rw [h0, zero_smul, zero_smul]
  · have hlt := l.2
    have hl' : l.1 = n + (l.1 - n) := by omega
    rw [hl', hga (l.1 - n) (by omega)]

private theorem fIdx_lt_add_of_lt_add {k₀ c n p : ℕ} (hp : p < n + c) : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

private theorem fIdx_injOn_of_lt_add {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p = PI.OneCosetSharp.LocE.fIdx k₀ c n p') : p = p' := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem mem_block_of_le_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c)
    (h : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p) : k₀ ≤ p ∧ p < k₀ + c := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem lt_or_le_of_fIdx_lt {k₀ c n p : ℕ} (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n) :
    p < k₀ ∨ k₀ + c ≤ p := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

private theorem allow_of_mem_block_of_le_right {k₀ m t N c p p' : ℕ} (hcm : c + 1 < m) (hp : k₀ ≤ p)
    (hpc : p < k₀ + c) (hp' : k₀ + c ≤ p') : PI.OneCosetSharp.Allow k₀ m t N p p' := by
  unfold PI.OneCosetSharp.Allow
  split_ifs
  · omega
  · left; omega
  · left; omega

theorem gaStep : GaStep := by
  intro k _ k₀ m t j n' c n hadm g hga hfree
  obtain ⟨hk₀, -, hm4, hj1, hjm, hc, hn', hn⟩ := hadm
  generalize j * t = s at hn
  generalize (j - 1) * t = s' at hn'
  have hkn : k₀ ≤ n := by omega
  have hcm : c + 1 < m := by omega
  obtain ⟨B, hB⟩ : ∃ B : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k),
      ∀ w, B w = AP (g (XP w)) :=
    ⟨AP ∘ₗ g.toLinearMap ∘ₗ XP, fun w => rfl⟩
  have hfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → g w = w :=
    fix_of_basis g hga
  have hB0 : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → B w = 0 := by
    intro w hw
    rw [hB, hw]
    simp
  have hBB : ∀ w, B (B w) = 0 := fun w => hB0 _ (by rw [hB]; exact XP_AP _)
  obtain ⟨κ, hκ, hκs⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ w, κ w = w + B w) ∧ ∀ w, κ.symm w = w - B w := by
    refine ⟨LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B) ?_ ?_, fun w => rfl, fun w => rfl⟩
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hBB, add_zero]
      abel
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, hBB, sub_zero]
      abel
  have hg : ∀ v, g v = g (XP v) + AP v := by
    intro v
    conv_lhs => rw [← lowProj_add_highProj (n := n) (c := c) v]
    rw [map_add (f := _), hfix _ (XP_AP v)]
  have hγ : ∀ v, (g * κ⁻¹) v = g (XP v) + AP v - AP (g (XP v)) := by
    intro v
    show g (κ.symm v) = _
    rw [hκs, map_sub, hfix (B v) (by rw [hB]; exact XP_AP _), hB, hg v]
  have hγl : ∀ v (l : Fin (n + c)), n ≤ l.1 → (g * κ⁻¹) v l = v l := by
    intro v l hl
    rw [hγ]
    simp only [Pi.sub_apply, Pi.add_apply, projA_apply, if_neg (not_lt.mpr hl)]
    ring
  have hγfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → (g * κ⁻¹) w = w := by
    intro w hw
    rw [hγ, hw]
    simp [projA_eq_self_of_projX_eq_zero hw]
  have hU : PI.OneCosetSharp.Loc.R1cond k n c (g * κ⁻¹) := by
    refine ⟨fun i v hv => ?_, hγfix _ (lowProj_basisVec_of_le n le_rfl), fun i => ?_⟩
    · rw [mem_Ufl] at hv ⊢
      intro l hl
      rw [hγl v l (by omega)]
      exact hv l hl
    · rw [hγfix _ (lowProj_basisVec_of_le (n + i) (Nat.le_add_right n i)), sub_self]
      exact Submodule.zero_mem _
  have hentry : ∀ p p' (hp : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c),
      PI.OneCosetSharp.ent k₀ c n c n κ.toLinearMap p p' =
        (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p') + B (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p'))) ⟨_, hp⟩ := by
    intro p p' hp
    simp only [PI.OneCosetSharp.ent, PI.OneCosetSharp.Loc.atN, dif_pos hp, LinearEquiv.coe_coe, hκ]
  have hBq : ∀ q (hq : q < n + c), B (PI.OneCosetSharp.Loc.eN k (n + c) q) ⟨q, hq⟩ = 0 := by
    intro q hq
    by_cases h : q < n
    · rw [hB, projA_apply]
      exact if_pos h
    · rw [hB0 _ (lowProj_basisVec_of_le q (not_lt.mp h))]
      rfl
  refine ⟨g * κ⁻¹, mem_flagUnipotent hU, κ, ⟨fun p' hp' => ?_, fun p p' hp hp' hne hent => ?_⟩, by simp⟩
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) (show p' < n + c by omega)
    rw [hentry p' p' hq, Pi.add_apply, hBq _ hq, add_zero, eN_apply]
    exact if_pos rfl
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) hp
    have hqq : PI.OneCosetSharp.LocE.fIdx k₀ c n p ≠ PI.OneCosetSharp.LocE.fIdx k₀ c n p' := fun h => hne (fIdx_injOn_of_lt_add hkn hp hp' h)
    rw [hentry p p' hq, Pi.add_apply, eN_apply, Fin.val_mk, if_neg hqq, zero_add] at hent
    by_cases hq'n : PI.OneCosetSharp.LocE.fIdx k₀ c n p' < n
    · rw [hB, lowProj_basisVec_of_lt _ hq'n] at hent
      rcases lt_or_le_of_fIdx_lt hq'n with h | h
      · obtain ⟨v, hv⟩ := hfree p' (by omega) (Or.inl h)
        rw [hv, projA_inX] at hent
        exact (hent rfl).elim
      · rw [projA_apply] at hent
        have hpn : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p := by
          by_contra h'
          exact hent (if_pos (not_le.mp h'))
        obtain ⟨hp1, hp2⟩ := mem_block_of_le_fIdx hkn hp hpn
        exact allow_of_mem_block_of_le_right hcm hp1 hp2 h
    · rw [hB0 _ (lowProj_basisVec_of_le _ (not_lt.mp hq'n))] at hent
      exact (hent rfl).elim

end PI.OneCosetSharp.W
end
end

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

private theorem det_eq_det_castLE_of_cols_eq_one {k : Type} [Field k] {a t N : ℕ} (hN : a + t = N)
    (K : Matrix (Fin N) (Fin N) k) (h0 : ∀ p q : Fin N, a ≤ q.1 → K p q = if p = q then 1 else 0) :
    K.det = (Matrix.of fun s s' : Fin a =>
      K (Fin.castLE (Nat.le.intro hN) s) (Fin.castLE (Nat.le.intro hN) s')).det := by
  subst hN
  have hK : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm K =
      Matrix.fromBlocks (Matrix.of fun s s' : Fin a => K (Fin.castAdd t s) (Fin.castAdd t s'))
        0 (Matrix.of fun (s : Fin t) (s' : Fin a) => K (Fin.natAdd a s) (Fin.castAdd t s')) 1 := by
    ext (s | s) (s' | s')
    · rfl
    · show K (Fin.castAdd t s) (Fin.natAdd a s') = 0
      rw [h0 (Fin.castAdd t s) (Fin.natAdd a s') (by simp), if_neg]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
    · show K (Fin.natAdd a s) (Fin.natAdd a s') = (1 : Matrix (Fin t) (Fin t) k) s s'
      rw [h0 (Fin.natAdd a s) (Fin.natAdd a s') (by simp), Matrix.one_apply]
      by_cases h : s = s'
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        have := congrArg Fin.val h'
        simp only [Fin.val_natAdd] at this
        exact Fin.ext (by omega)
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm K, hK, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one]
  rfl

private theorem allow_mono {k₀ m t a b p q : ℕ} (hab : a ≤ b) (h : PI.OneCosetSharp.Allow k₀ m t a p q) :
    PI.OneCosetSharp.Allow k₀ m t b p q := by
  unfold PI.OneCosetSharp.Allow at h ⊢
  split_ifs at h ⊢
  · exact h
  · exact h
  · rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_lt_of_le h1 hab, h2⟩

theorem kappaZero : KappaZero := by
  intro k inst ψ₀ χ k₀ m t j n' c n hadm y hy
  obtain ⟨hk, hr⟩ := PI.OneCosetSharp.W.P2.nums_le hadm
  obtain ⟨-, -, -, hj1, -, -, hdom, hcod⟩ := hadm
  have hN : k₀ + m - 1 + (j - 1) * t + t = n + c := by
    rw [hcod]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    generalize k₀ + m - 1 = r
    ring
  have key : (∀ p', p' < k₀ + m - 1 → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p p' ≠ 0 →
        PI.OneCosetSharp.Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p') ∧
      (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
        PI.OneCosetSharp.ent k₀ (c + 1) n' c n y s.1 s'.1).det ≠ 0 := by
    simp only [PI.OneCosetSharp.PhiS] at hy
    split_ifs at hy with hcond
    · refine ⟨hcond.1, hcond.2, fun hdet => hy ?_⟩
      rw [hdet]
      simp [PI.OneCosetSharp.chiV]
    · exact absurd rfl hy
  have hcoord : ∀ (v : Fin (n + c) → k) (l : Fin (n + c)), PI.OneCosetSharp.Loc.atN v l.1 = v l := fun v l => by
    simp only [PI.OneCosetSharp.Loc.atN, dif_pos l.2, Fin.eta]
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin (n + c)) (Fin (n + c)) k, ∀ p q, K p q =
      if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1 else if p = q then 1 else 0 :=
    ⟨Matrix.of fun p q => if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1
      else if p = q then 1 else 0, fun _ _ => rfl⟩
  have hdetK : K.det ≠ 0 := by
    rw [det_eq_det_castLE_of_cols_eq_one hN K (fun p q hq => by rw [hK, if_neg (not_lt.mpr hq)])]
    refine ne_of_eq_of_ne ?_ key.2.2
    congr 1
    ext s s'
    simp only [Matrix.of_apply]
    rw [hK, if_pos] <;> first | rfl | exact s'.2
  have hA : IsUnit (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm
      (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm).det := by
    rw [Matrix.det_submatrix_equiv_self]
    exact isUnit_iff_ne_zero.mpr hdetK
  obtain ⟨κ, hκ⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), κ.toLinearMap =
      Matrix.toLin' (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm) :=
    ⟨Matrix.toLinearEquiv' _ (Matrix.invertibleOfIsUnitDet _ hA), rfl⟩
  have hperm : PI.OneCosetSharp.W.P2.Pm k₀ hk κ = K := by
    unfold PI.OneCosetSharp.W.P2.Pm
    rw [hκ, LinearMap.toMatrix'_toLin']
    ext p q
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨κ, ?_, ?_⟩
  · rw [PI.OneCosetSharp.W.P2.injs_iff hk hr κ, hperm, PI.OneCosetSharp.W.P2.mem_alg]
    refine ⟨fun p q hpq => ?_, fun p hp => ?_⟩
    · by_cases hpq' : p = q
      · exact Or.inl (congrArg Fin.val hpq')
      · refine Or.inr ?_
        have hne : p.1 ≠ q.1 := fun h => hpq' (Fin.ext h)
        by_cases hq : q.1 < k₀ + m - 1 + (j - 1) * t
        · rw [hK, if_pos hq] at hpq
          exact allow_mono (Nat.le.intro hN) (key.2.1 p.1 q.1 p.2 hq hne hpq)
        · rw [hK, if_neg hq, if_neg hpq'] at hpq
          exact absurd rfl hpq
    · have hpa : p.1 < k₀ + m - 1 + (j - 1) * t := by omega
      rw [hK, if_pos hpa]
      exact key.1 p.1 hp
  · intro p hp
    have hpa : p < k₀ + m - 1 + (j - 1) * t := by omega
    have hpN : p < n + c := by omega
    funext l
    have hl : PI.OneCosetSharp.LocE.fIdx k₀ c n ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l).1 = l.1 :=
      congrArg Fin.val ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).apply_symm_apply l)
    have e1 := PI.OneCosetSharp.W.P2.ent_eq hk κ ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l) ⟨p, hpN⟩
    rw [hperm, hK, if_pos hpa] at e1
    unfold PI.OneCosetSharp.ent at e1
    rw [hl, hcoord, hcoord] at e1
    exact e1

end PI.OneCosetSharp.W
