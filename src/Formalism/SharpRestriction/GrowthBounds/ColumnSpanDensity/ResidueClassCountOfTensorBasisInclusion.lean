module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.EdgeLatRS
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsRetractionBasis

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ResidueClassCountOfTensorBasisInclusion
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems Formalism.GradedWeylDivisibility

theorem filter_lt_one (m : ℕ) : (Finset.univ.filter fun a : Fin (m + 1) => a.val < 1) = {0} := by
  ext a
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨-, h⟩
    exact Fin.ext (by simpa using Nat.lt_one_iff.1 h)
  · rintro rfl
    exact ⟨Finset.mem_univ _, by simp⟩

theorem lamAt_abs {n' m : ℕ} (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) (s : Fin n')
    (i : Fin (m + 1)) : |lamAt lamO s i| ≤ c := by
  unfold lamAt
  split_ifs
  · exact h s i
  · rw [abs_neg]; exact h s _

section

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

def Elast (lamO : Fin n' → Fin (m + 1) → ℤ) : ℤ := ∑ s, lamAt lamO s (Fin.last m)

theorem Ar_sub_le (lamO : Fin n' → Fin (m + 1) → ℤ) (c : ℕ) (h : ∀ s i, |lamO s i| ≤ c) :
    Ar 1 lamO - Elast lamO ≤ ((2 * n' * c : ℕ) : ℤ) := by
  unfold Ar Elast
  rw [← Finset.sum_sub_distrib]
  have h1 : ∀ s ∈ (Finset.univ : Finset (Fin n')),
      (∑ i : Fin (m + 1) with i.val < 1, lamAt lamO s i) - lamAt lamO s (Fin.last m) ≤ 2 * (c : ℤ) := by
    intro s _
    rw [filter_lt_one, Finset.sum_singleton]
    have h2 := abs_le.1 (lamAt_abs lamO c h s 0)
    have h3 := abs_le.1 (lamAt_abs lamO c h s (Fin.last m))
    linarith [h2.2, h3.1]
  have h4 := Finset.sum_le_sum h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h4
  refine le_trans h4 ?_
  push_cast
  rw [nsmul_eq_mul]
  linarith

theorem steps_rev (lamO : Fin n' → Fin (m + 1) → ℤ) (hdom : IsDominant lamO) (e : Edge R.W R.Qq (m + 1))
    (he : IsEdge p n' 1 e) :
    (∀ P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.src)) ∧
    (∀ P ∈ Hten R.O lamO (fun s => extO R.O R.ι R.σ s.val e.tgt),
      (algebraMap R.O R.Kf R.w ^ (-Elast lamO)) • P ∈ Hten R.O lamO (fun s => LeAt p R.ι R.σ R.w s.val e)) := by
  obtain ⟨gs, hgs, h1, h2, h3⟩ := edgeLat_RS R e he
  have hw := R.w_ne
  have hinj : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hA : ∏ s : Fin n', algebraMap R.O R.Kf R.w ^ (-lamAt lamO s (Fin.last m)) =
      algebraMap R.O R.Kf R.w ^ (-Elast lamO) := by
    rw [lb_zpow_sum _ hw, Elast, Finset.sum_neg_distrib]
  have hgD : ∀ s, IsUnit (gs s * lb_D (m + 1) 1 (algebraMap R.O R.Kf R.w)).det := by
    intro s
    rw [Matrix.det_mul]; exact (hgs s).mul (lb_D_det _ _ _ hw)
  have hone : ∀ z : ℤ, -(((Finset.univ.filter fun a : Fin (m + 1) => a.val < 1).card : ℤ) * z) = -z := by
    intro z
    rw [filter_lt_one]
    simp
  constructor
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h2] at hF
    rw [h1]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgs _) F hF
    rwa [hone] at this
  · intro P hP
    rw [← hA]
    refine lb_tensor R.O R.Kf _ _ _ (fun s F hF => ?_) P hP
    beta_reduce at hF ⊢
    rw [h3] at hF
    rw [h2]
    have := zpow_smul_mem_H0_colSpan_of_mem_colSpan_mul R.O R.Kf hinj m 1 _ (kp_lamAt_antitone _ hdom s) R.w hw _ (hgD _) F hF
    rwa [hone] at this

end

theorem restOrdBound : RestOrdBound := by
  intro p n' R m lamO c hdom hsmall e he
  obtain ⟨hs1, hs2⟩ := steps_rev R lamO hdom e he
  have hw := R.w_ne
  set wK : R.Kf := algebraMap R.O R.Kf R.w with hwK
  have hle := Ar_sub_le lamO c hsmall
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (k₀ : ℤ) = ((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO) :=
    ⟨(((2 * n' * c : ℕ) : ℤ) - (Ar 1 lamO - Elast lamO)).toNat, Int.toNat_of_nonneg (by linarith)⟩
  constructor
  · rintro _ ⟨h, hh, rfl⟩
    have h1 : wK ^ (-Elast lamO) • h ∈ HL (O := R.O) R.ι R.σ lamO e.src := hs1 _ hh
    refine ⟨R.w ^ k₀ • (wK ^ (-Elast lamO) • h), Submodule.smul_mem _ _ h1, ?_⟩
    show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (R.w ^ k₀ • (wK ^ (-Elast lamO) • h)) = wK ^ (-Ar 1 lamO) • h
    rw [← algebraMap_smul R.Kf (R.w ^ k₀), map_pow, ← hwK, smul_smul, smul_smul, ← zpow_natCast wK k₀, hk₀,
      ← zpow_add₀ hw, ← zpow_add₀ hw]
    congr 2
    ring
  · rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ, ?_, ?_⟩
    · intro h hh
      have h1 : wK ^ (-Elast lamO) • h ∈ HLe p R.ι R.σ R.w lamO e := hs2 _ hh
      obtain ⟨a, ha⟩ := hφ _ h1
      refine ⟨R.w ^ k₀ * a, ?_⟩
      rw [map_smul, smul_eq_mul] at ha
      rw [map_mul, ha, map_pow, ← hwK, LinearMap.smul_apply, smul_eq_mul, ← zpow_natCast wK k₀, hk₀, ← mul_assoc,
        ← zpow_add₀ hw]
      congr 2
      ring
    · show wK ^ (-((2 * n' * c : ℕ) : ℤ)) • (wK ^ (((2 * n' * c : ℕ) : ℤ) - Ar 1 lamO) • φ) = wK ^ (-Ar 1 lamO) • φ
      rw [smul_smul, ← zpow_add₀ hw]
      congr 2
      ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeMapsOfFunctorComparison
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def LatticeFunctorComparison : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (m : ℕ), 2 ≤ m → ∀ (TT : Finset (Fin n')) (a : ℕ) (A B : TT → ℕ),
    (∀ s, A s + B s + 1 ≤ 8 * a) →
    ∃ (io : ∀ j : TT → ℕ, Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s)) →ₗ[R.Kf]
        VHH (m := m) R.Kf TT (ex A) (ex B))
      (pr : ∀ j : TT → ℕ, VHH (m := m) R.Kf TT (ex A) (ex B) →ₗ[R.Kf]
        Vsp R.Kf (flatW m (fun s => A s - j s) (fun s => B s - j s))),
      (∀ x, ∑ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)), io j (pr j x) = x) ∧
      ∀ M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf), (∀ s, IsLattice R.O (M s)) →
        ∀ j ∈ Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)),
        (∀ x ∈ toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M),
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • pr j x ∈
            toV (flatW m (fun s => A s - j s) (fun s => B s - j s))
              (Hten R.O (flatW m (fun s => A s - j s) (fun s => B s - j s)) M)) ∧
        (∀ y ∈ toV (flatW m (fun s => A s - j s) (fun s => B s - j s))
              (Hten R.O (flatW m (fun s => A s - j s) (fun s => B s - j s)) M),
          ((p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊)) • io j y ∈
            toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M))

theorem Ar_le_AHH {n' : ℕ} (m : ℕ) (hm : 1 ≤ m) (TT : Finset (Fin n')) (A B j : TT → ℕ) :
    Ar 1 (flatW m (fun s => A s - j s) (fun s => B s - j s)) ≤ AHH TT (ex A) (ex B) := by
  have h0 : (Finset.univ.filter fun i : Fin (m + 1) => i.val < 1) = {0} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      exact Fin.ext (by rw [Fin.val_zero]; omega)
    · intro h
      subst h
      rw [Fin.val_zero]
      omega
  have hl : (Fin.last m : Fin (m + 1)) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    rw [Fin.val_last, Fin.val_zero] at this
    omega
  have key : ∀ s : Fin n',
      (∑ i ∈ Finset.univ.filter (fun i : Fin (m + 1) => i.val < 1),
        lamAt (flatW m (fun s => A s - j s) (fun s => B s - j s)) s i) ≤
        if s ∈ TT then (hhDeg (ex A) (ex B) s true : ℤ) else 0 := by
    intro s
    rw [h0, Finset.sum_singleton]
    by_cases hs : s ∈ TT
    · have hA : ex A s = A ⟨s, hs⟩ := dif_pos hs
      have hB : ex B s = B ⟨s, hs⟩ := dif_pos hs
      have f0 : flatW m (fun s => A s - j s) (fun s => B s - j s) s 0 = ((A ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ) := by
        simp [flatW, hs]
      have fl : flatW m (fun s => A s - j s) (fun s => B s - j s) s (Fin.last m) =
          -((B ⟨s, hs⟩ - j ⟨s, hs⟩ : ℕ) : ℤ) := by
        simp [flatW, hs, hl]
      rw [if_pos hs]
      unfold lamAt hhDeg
      rw [if_pos rfl, hA, hB]
      by_cases he : Even s.val
      · rw [if_pos he, if_pos he, f0]
        exact_mod_cast Nat.sub_le _ _
      · rw [if_neg he, if_neg he]
        beta_reduce
        rw [Fin.rev_zero, fl, neg_neg]
        exact_mod_cast Nat.sub_le _ _
    · have hz : ∀ i, flatW m (fun s => A s - j s) (fun s => B s - j s) s i = 0 := fun i => by
        simp [flatW, hs]
      rw [if_neg hs]
      unfold lamAt
      by_cases he : Even s.val
      · rw [if_pos he, hz]
      · rw [if_neg he]
        beta_reduce
        rw [hz, neg_zero]
  unfold Ar AHH
  calc _ ≤ ∑ s : Fin n', (if s ∈ TT then (hhDeg (ex A) (ex B) s true : ℤ) else 0) :=
        Finset.sum_le_sum fun s _ => key s
    _ = _ := by rw [Finset.sum_ite_mem, Finset.univ_inter]

section Formal

variable {O Kf V : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup V] [Module Kf V] [Module O V]
  [IsScalarTower O Kf V]

theorem scale_add_le (w : O) (hw : algebraMap O Kf w ≠ 0) (a d : ℤ) (hd : 0 ≤ d) (M : Submodule O V) :
    scale (algebraMap O Kf w ^ (a + d)) M ≤ scale (algebraMap O Kf w ^ a) M := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  unfold scale
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨(w ^ k) • x, M.smul_mem _ hx, ?_⟩
  simp only [LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  rw [zpow_add₀ hw, zpow_natCast, mul_smul, ← map_pow, algebraMap_smul]

end Formal

theorem lattice_maps_of_functor_comparison (h : LatticeFunctorComparison) : RhoSumLatticeMaps := by
  classical
  intro p n' R m hm TT a A B hdeg
  obtain ⟨io, pr, hsum, hL⟩ := h p n' R m hm TT a A B hdeg
  generalize hu : TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊ = u at hL
  set ω : R.Kf := algebraMap R.O R.Kf R.w with hω
  have hω0 : ω ≠ 0 := R.w_ne
  have hpω : (p : R.Kf) = ω ^ 2 := R.p_eq
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  let d : (TT → ℕ) → ℤ := fun j => AHH TT (ex A) (ex B) - Ar 1 (lamj j)
  have hd : ∀ j, 0 ≤ d j := fun j => sub_nonneg.2 (Ar_le_AHH m (by omega) TT A B j)
  refine ⟨fun j => (ω ^ (-d j)) • io j, fun j => (ω ^ (d j)) • pr j, ?_, ?_⟩
  · intro x
    rw [← hsum x]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsum x]
    simp only [LinearMap.smul_apply, map_smul, smul_smul]
    rw [← zpow_add₀ hω0]
    simp
  intro t c e he j hj

  have src : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) x,
      x ∈ scale (ω ^ E) (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M)) →
      ((p : R.Kf) ^ u) • ((ω ^ (d j)) • pr j) x ∈ scale (ω ^ (E + d j)) (toV (lamj j) (Hten R.O (lamj j) M)) := by
    rintro M hM E x ⟨x0, hx0, rfl⟩
    refine ⟨_, (hL M hM j hj).1 x0 hx0, ?_⟩
    show ω ^ (E + d j) • ((p : R.Kf) ^ u • pr j x0) = (p : R.Kf) ^ u • ((ω ^ (d j)) • pr j) (ω ^ E • x0)
    rw [LinearMap.smul_apply, map_smul, smul_smul, smul_smul, smul_smul, zpow_add₀ hω0]
    congr 1
    ring
  have tst : ∀ (M : Fin n' → Submodule R.O (Fin (m + 1) → R.Kf)), (∀ s, IsLattice R.O (M s)) → ∀ (E : ℤ) Φ,
      Φ ∈ scale (ω ^ E) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) M))) →
      ((p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j))) • (Φ ∘ₗ ((ω ^ (-d j)) • io j)) ∈
        scale (ω ^ (E + d j)) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf (toV (lamj j) (Hten R.O (lamj j) M))) := by
    rintro M hM E Φ ⟨Φ0, hΦ0, rfl⟩
    refine ⟨((p : R.Kf) ^ (2 * u)) • (Φ0 ∘ₗ io j), ?_, ?_⟩
    · intro y hy
      obtain ⟨b, hb⟩ := hΦ0 _ ((hL M hM j hj).2 y hy)
      refine ⟨(p : R.O) ^ u * b, ?_⟩
      rw [map_mul, hb, map_pow, map_natCast, LinearMap.smul_apply, LinearMap.comp_apply, map_smul]
      simp only [smul_eq_mul]
      ring
    · show ω ^ (E + d j) • ((p : R.Kf) ^ (2 * u) • (Φ0 ∘ₗ io j)) =
        (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) •
          ((ω ^ E • Φ0) ∘ₗ ((ω ^ (-d j)) • io j))
      ext y
      simp only [LinearMap.smul_apply, LinearMap.comp_apply, smul_eq_mul, map_smul]
      have e1 : (p : R.Kf) ^ (((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j)) =
          (p : R.Kf) ^ (2 * u) * ω ^ (d j) * ω ^ (d j) := by
        have hp0 : (p : R.Kf) ≠ 0 := by rw [hpω]; exact pow_ne_zero _ hω0
        have : ((2 * u : ℕ) : ℤ) + AHH TT (ex A) (ex B) - Ar 1 (lamj j) = ((2 * u : ℕ) : ℤ) + d j := by
          simp only [d]; ring
        rw [this, zpow_add₀ hp0, zpow_natCast, mul_assoc]
        congr 1
        rw [hpω, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hω0]
        congr 1
        push_cast
        ring
      rw [e1, zpow_add₀ hω0, zpow_neg]
      have hne : ω ^ (d j) ≠ 0 := zpow_ne_zero _ hω0
      field_simp

  have latE : ∀ e' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e' →
      (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.src)) ∧
      (∀ s : Fin n', IsLattice R.O (LeAt p R.ι R.σ R.w s.val e')) ∧
      (∀ s : Fin n', IsLattice R.O (extO R.O R.ι R.σ s.val e'.tgt)) := by
    intro e' he'
    obtain ⟨gs, hg, h1, h2, h3⟩ := edgeLat_RS R e' he'
    have hD : IsUnit (Formalism.MainNotions.G.LatticeSystems.lb_D (m + 1) 1 ω).det := Formalism.MainNotions.G.LatticeSystems.lb_D_det _ _ _ hω0
    refine ⟨fun s => ⟨gs s.val, hg _, h1 _⟩, fun s => ⟨_, ?_, h2 _⟩, fun s => ⟨_, ?_, h3 _⟩⟩
    · rw [Matrix.det_mul]; exact (hg _).mul hD
    · rw [Matrix.det_mul, Matrix.det_mul]; exact ((hg _).mul hD).mul hD
  have hAr : ∀ E : ℤ, E + -AHH TT (ex A) (ex B) + d j = E + -Ar 1 (lamj j) := fun E => by simp only [d]; ring
  constructor
  · intro x hx
    obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact scale_add_le R.w hω0 _ _ (hd j) _ (src _ (latE e he).1 _ x hx1)
    · have := src _ (latE e he).2.1 _ x hx2
      have e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j) := by simp only [d]; ring
      rw [e2] at this
      exact this
    · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)
      have hx4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 hx3) e') hc
      obtain ⟨x1, ⟨x0, hx0, rfl⟩, hx5⟩ := hx4
      have hx6 : x ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)))
          (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e')) := by
        refine ⟨x0, hx0, ?_⟩
        rw [← hx5]
        show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • x0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • x0)
        rw [smul_smul, zpow_add₀ hω0]
      obtain ⟨y0, hy0, hy1⟩ := src _ (latE e' hc.1).2.1 _ x hx6
      rw [hAr] at hy1
      refine ⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩
      rw [← hy1]
      show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0
      rw [smul_smul, zpow_add₀ hω0]
  · intro Φ hΦ
    obtain ⟨⟨h1, h2⟩, h3⟩ := hΦ
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact scale_add_le R.w hω0 _ _ (hd j) _ (tst _ (latE e he).2.2 _ Φ h1)
    · have := tst _ (latE e he).2.1 _ Φ h2
      have e2 : -AHH TT (ex A) (ex B) + d j = -Ar 1 (lamj j) := by simp only [d]; ring
      rw [e2] at this
      exact this
    · refine SetLike.mem_coe.2 ((Submodule.mem_iInf _).2 fun e' => (Submodule.mem_iInf _).2 fun hc => ?_)
      have h4 := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (SetLike.mem_coe.1 h3) e') hc
      obtain ⟨Φ1, ⟨Φ0, hΦ0, rfl⟩, h5⟩ := h4
      have h6 : Φ ∈ scale (ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B))) (Formalism.GradedWeylDivisibility.dualLat R.O R.Kf
          (toVHH TT (ex A) (ex B) (HHten R.O TT (ex A) (ex B) fun s => LeAt p R.ι R.σ R.w s.val e'))) := by
        refine ⟨Φ0, hΦ0, ?_⟩
        rw [← h5]
        show ω ^ ((c : ℤ) + -AHH TT (ex A) (ex B)) • Φ0 = ω ^ (c : ℤ) • (ω ^ (-AHH TT (ex A) (ex B)) • Φ0)
        rw [smul_smul, zpow_add₀ hω0]
      obtain ⟨y0, hy0, hy1⟩ := tst _ (latE e' hc.1).2.1 _ Φ h6
      rw [hAr] at hy1
      refine ⟨ω ^ (-Ar 1 (lamj j)) • y0, ⟨y0, hy0, rfl⟩, ?_⟩
      rw [← hy1]
      show ω ^ (c : ℤ) • (ω ^ (-Ar 1 (lamj j)) • y0) = ω ^ ((c : ℤ) + -Ar 1 (lamj j)) • y0
      rw [smul_smul, zpow_add₀ hω0]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudPropOfMapsBasis
namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem latRetract : LatRetract := by
  unfold LatRetract
  intro O K V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι ι' _ _ b b' io hio
  classical
  set L := Submodule.span O (Set.range b) with hL
  set L' := Submodule.span O (Set.range b') with hL'
  have hcoord : ∀ x ∈ L, ∀ i, ∃ a : O, algebraMap O K a = b.repr x i := by
    intro x hx i
    exact ⟨(b.restrictScalars O).repr ⟨x, hx⟩ i, Module.Basis.restrictScalars_repr_apply O b ⟨x, hx⟩ i⟩
  have hinj : Function.Injective io := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    rw [LinearMap.mem_ker] at hF
    by_contra hne
    obtain ⟨i, hi⟩ : ∃ i, b.repr F i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hne (b.ext_elem (fun j => by simp [h j]))
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
    have hϖ0 : algebraMap O K ϖ ≠ 0 := fun h0 =>
      hϖ.ne_zero (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hmem : ((algebraMap O K ϖ)⁻¹ * (b.repr F i)⁻¹) • F ∈ L := by
      rw [← hio, map_smul, hF, smul_zero]
      exact Submodule.zero_mem _
    obtain ⟨a, ha⟩ := hcoord _ hmem i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hi, mul_one] at ha
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨a, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, ha, map_one, mul_inv_cancel₀ hϖ0]
  let φ : L →ₗ[O] L' :=
    LinearMap.codRestrict L' ((io.restrictScalars O).domRestrict L) (fun x => (hio x).2 x.2)
  have hφ : Function.Injective φ := fun x y h => Subtype.ext (hinj (congrArg Subtype.val h))
  haveI : Module.Finite O L' := Module.Finite.span_of_finite O (Set.finite_range b')
  haveI : NoZeroSMulDivisors O (L' ⧸ LinearMap.range φ) := by
    refine ⟨fun {a q} h => ?_⟩
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
    rcases eq_or_ne a 0 with ha | ha
    · exact Or.inl ha
    right
    rw [Submodule.Quotient.mk_eq_zero]
    obtain ⟨x, hx⟩ := h
    have hx' : io (x : V) = a • (y : V') := congrArg Subtype.val hx
    have hK : algebraMap O K a ≠ 0 := fun h0 =>
      ha (IsFractionRing.injective O K (by rw [h0, map_zero]))
    have hyio : (y : V') = io ((algebraMap O K a)⁻¹ • (x : V)) := by
      rw [map_smul, hx', ← algebraMap_smul K a (y : V'), smul_smul, inv_mul_cancel₀ hK, one_smul]
    have hmem : (algebraMap O K a)⁻¹ • (x : V) ∈ L := (hio _).1 (hyio ▸ y.2)
    exact ⟨⟨_, hmem⟩, Subtype.ext hyio.symm⟩
  haveI : Module.Free O (L' ⧸ LinearMap.range φ) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (LinearMap.range φ).mkQ LinearMap.id
    (Submodule.mkQ_surjective _)
  let pr : L' →ₗ[O] L' := LinearMap.id - s ∘ₗ (LinearMap.range φ).mkQ
  have hpr : ∀ y, pr y ∈ LinearMap.range φ := by
    intro y
    have h2 := LinearMap.congr_fun hs ((LinearMap.range φ).mkQ y)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2
    rw [← Submodule.ker_mkQ (LinearMap.range φ), LinearMap.mem_ker]
    simp only [pr, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, h2, sub_self]
  let e := LinearEquiv.ofInjective φ hφ
  let r0 : L' →ₗ[O] L := e.symm.toLinearMap ∘ₗ LinearMap.codRestrict (LinearMap.range φ) pr hpr
  have hr0 : ∀ x : L, r0 (φ x) = x := by
    intro x
    have h1 : (LinearMap.range φ).mkQ (φ x) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact LinearMap.mem_range_self φ x
    show e.symm (LinearMap.codRestrict _ pr hpr (φ x)) = x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp [LinearMap.codRestrict_apply, h1, e, pr, LinearEquiv.ofInjective_apply]
  let ret : V' →ₗ[K] V := b'.constr K (fun j => ((r0 ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ : L) : V))
  have hA : ∀ y : L', ret (y : V') = (r0 y : V) := by
    have h3 : (ret.restrictScalars O) ∘ₗ L'.subtype = L.subtype ∘ₗ r0 := by
      refine (b'.restrictScalars O).ext (fun j => ?_)
      have hj : (b'.restrictScalars O) j = ⟨b' j, Submodule.subset_span ⟨j, rfl⟩⟩ :=
        Subtype.ext (Module.Basis.restrictScalars_apply _ _ _)
      rw [hj]
      simp [ret, Module.Basis.constr_basis]
    intro y
    exact LinearMap.congr_fun h3 y
  refine ⟨ret, ?_, ?_⟩
  · have h4 : ret ∘ₗ io = LinearMap.id := by
      refine b.ext (fun i => ?_)
      have hbi : b i ∈ L := Submodule.subset_span ⟨i, rfl⟩
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      have h5 := hA (φ ⟨b i, hbi⟩)
      rw [hr0] at h5
      exact h5
    intro F
    exact LinearMap.congr_fun h4 F
  · intro G hG
    rw [hA ⟨G, hG⟩]
    exact (r0 ⟨G, hG⟩).2

theorem cloud_prop_of_maps_basis (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl :=
  cloud_prop_of_maps_retraction_basis hC latRetract hBP hD3

theorem cloud_bound_of_maps (hC : RestCloudMaps) (hBP : BePerfect) (hD3 : DualHeightBasis) (hW : WeylV) : CloudWeightLowerBound :=
  cloud_bound_of_prop_and_weyl_dimension (cloud_prop_of_maps_basis hC hBP hD3) hW

end Formalism.MainNotions.flipOneThree.Pf
end
