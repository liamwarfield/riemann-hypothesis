module

public import Development.EtaleCohomology.KummerTheory.LocalHomotopyEtaleCohomology
public import Development.EtaleCohomology.KummerTheory.FinSHInv
public import Development.EtaleCohomology.KummerTheory.FinStalk
public import Development.EtaleCohomology.KummerTheory.FinBock
public import Development.EtaleCohomology.WeilConjectures.AdicFinPf

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.LimitPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimExtHl : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ),
  ∃ e : Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i,
    ∀ x y k, lev l (e x y) k = ext (l ^ k) pX pY a n i (lev l x k) (lev l y k)

def LimLH : Prop := A11 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i),
  (∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0)) →
  (∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n)) →
  ∃ Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i,
    (∀ y k, lev l (Φ y) k = lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k)) ∧
    IsoUpTo N Φ

def LimAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M N : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → 0 < N → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) → IsoUpTo N Φ →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

theorem Limit_of (h1 : LimExtHl) (h2 : LimLH) (h3 : LimAssemble) : Limit := by
  intro hA9 hA11 l _ X Y S pX pY n i M N r c hnM hN hB hfin hiso
  choose e he using fun a : ℤ => h1 hA11 l pX pY a n i
  obtain ⟨Φ, hΦ, hΦN⟩ := h2 hA11 l pX pY n i M N r c hfin hiso
  have key : ∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s) := by
    intro y
    apply Subtype.ext
    funext k
    change lev l (Φ y) k = _
    rw [hΦ y k, Submodule.coe_sum, Finset.sum_apply]
    unfold lh
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    exact (he _ _ _ k).symm
  obtain ⟨κ, hκ⟩ := h3 hA9 l pX pY n i M N r c hnM hN hB e Φ key hΦN
  exact ⟨κ, fun a x y => ⟨e a x y, fun k => he a x y k, hκ a x y⟩⟩

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.FinAdicDeg
section -- merged from Development.EtaleCohomology.KummerTheory.AdicAlgPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.KummerTheory

section Alg
variable (l : ℕ) [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M]

theorem adic_decomp [Module.Finite ℤ_[l] M] : ∃ (r : ℕ) (c : Fin r → M) (e : ℕ), 0 < e ∧
    LinearIndependent ℤ_[l] c ∧ ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0 := by
  classical
  set T := Submodule.torsion ℤ_[l] M
  have hTfin : Module.Finite ℤ_[l] T := inferInstance
  obtain ⟨a, ha, ha0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors (Submodule.torsion_isTorsion (R := ℤ_[l]) (M := M))
  have hane : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  have hkill : ∀ τ ∈ T, (l ^ a.valuation : ℕ) • τ = 0 := by
    intro τ hτ
    have h1 : a • (⟨τ, hτ⟩ : T) = 0 := Submodule.mem_annihilator.mp ha _ Submodule.mem_top
    have h2 : a • τ = 0 := congrArg Subtype.val h1
    rw [PadicInt.unitCoeff_spec hane, mul_smul] at h2
    have h3 := congrArg (fun v => (((PadicInt.unitCoeff hane)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • v) h2
    simp only [smul_zero, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h3
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]
    push_cast
    exact h3
  set Q := M ⧸ T
  let b := Module.finBasis ℤ_[l] Q
  let c : Fin (Module.finrank ℤ_[l] Q) → M := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose
  have hc : ∀ s, T.mkQ (c s) = b s := fun s => (Submodule.Quotient.mk_surjective T (b s)).choose_spec
  have hcomp : T.mkQ ∘ c = b := funext hc
  refine ⟨_, c, l ^ a.valuation, pow_pos (Fact.out : l.Prime).pos _, ?_, ?_⟩
  · exact LinearIndependent.of_comp T.mkQ (hcomp ▸ b.linearIndependent)
  · intro x
    refine ⟨b.repr (T.mkQ x), x - ∑ s, b.repr (T.mkQ x) s • c s, by abel, hkill _ ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
    simp only [map_smul, hc]
    rw [b.sum_repr, sub_self]

theorem adic_qbasis {r : ℕ} (c : Fin r → M) (e : ℕ) (he : 0 < e) (hli : LinearIndependent ℤ_[l] c)
    (hdec : ∀ x : M, ∃ (a : Fin r → ℤ_[l]) (τ : M), x = ∑ s, a s • c s + τ ∧ e • τ = 0) :
    LinearIndependent ℚ_[l] (fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) ∧
    Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c s : ℚ_[l] ⊗[ℤ_[l]] M)) = ⊤ := by
  let f := TensorProduct.mk ℤ_[l] ℚ_[l] M 1
  refine ⟨hli.of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f, ?_⟩
  have htop := span_eq_top_of_isLocalizedModule ℚ_[l] (nonZeroDivisors ℤ_[l]) f (v := Set.univ) Submodule.span_univ
  refine top_unique (htop ▸ Submodule.span_le.mpr ?_)
  rintro _ ⟨x, -, rfl⟩
  obtain ⟨a, τ, rfl, hτ⟩ := hdec x
  have hfτ : f τ = 0 := by
    have h1 : (e : ℚ_[l]) • f τ = 0 := by rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hτ, map_zero]
    exact (smul_eq_zero.mp h1).resolve_left (Nat.cast_ne_zero.mpr he.ne')
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), hfτ, add_zero, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [map_smul]
  exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)

end Alg

def levH (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ) (k : ℕ) : Hl l E n i →+ Ht (l ^ k) E n i where
  toFun x := lev l x k
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lev_comb (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} {r : ℕ} (c : Fin r → Hl l E n i) (a : Fin r → ℤ_[l]) (k : ℕ) :
    lev l (∑ s, a s • c s) k = comb (l ^ k) (fun s => lev l (c s) k) (fun s => PadicInt.toZModPow k (a s)) := by
  change levH l E n i k _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  rfl

theorem AdicAlg_of : AdicAlg := by
  intro l _ E n i hfin hker M hM hcok
  obtain ⟨r, c, e, he, hli, hdec⟩ := adic_decomp l (M := Hl l E n i)
  refine ⟨r, c, e * M, Nat.mul_pos he hM, adic_qbasis l c e he hli hdec, fun k => ⟨?_, ?_⟩⟩
  · intro t ht
    have : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    let a : Fin r → ℤ_[l] := fun s => ((t s).val : ℤ_[l])
    have hat : (fun s => PadicInt.toZModPow k (a s)) = t := funext fun s => by simp [a]
    have hx : lev l (∑ s, a s • c s) k = 0 := by rw [lev_comb, hat]; exact ht
    obtain ⟨y, hy⟩ := hker k _ hx
    obtain ⟨b, τ, rfl, hτ⟩ := hdec y
    have heq : ∑ s, ((e : ℤ_[l]) * a s - (e : ℤ_[l]) * (l : ℤ_[l]) ^ k * b s) • c s = 0 := by
      have h1 := congrArg (fun v => (e : ℤ_[l]) • v) hy
      simp only [smul_add, Finset.smul_sum, smul_smul] at h1
      have h2 : (e : ℤ_[l]) • (l : ℤ_[l]) ^ k • τ = 0 := by
        rw [smul_comm, Nat.cast_smul_eq_nsmul, hτ, smul_zero]
      rw [smul_smul] at h2
      rw [h2, add_zero] at h1
      simp only [sub_smul, Finset.sum_sub_distrib, h1, mul_assoc, sub_self]
    have hs := Fintype.linearIndependent_iff.mp hli _ heq
    have ht0 : t = 0 := by
      funext s
      have h3 : a s = (l : ℤ_[l]) ^ k * b s := by
        have h4 := hs s
        rw [sub_eq_zero, mul_assoc] at h4
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr he.ne') h4
      rw [← congrFun hat s]
      simp only [h3, map_mul, map_pow, map_natCast, Pi.zero_apply]
      rw [show ((l : ZMod (l ^ k)) ^ k) = ((l ^ k : ℕ) : ZMod (l ^ k)) by push_cast; rfl, ZMod.natCast_self, zero_mul]
    rw [ht0, smul_zero]
  · intro z
    obtain ⟨x, hx⟩ := hcok k z
    obtain ⟨a, τ, rfl, hτ⟩ := hdec x
    refine ⟨fun s => PadicInt.toZModPow k ((e : ℤ_[l]) * a s), ?_⟩
    rw [← lev_comb, mul_smul, ← hx]
    have key : ∀ w, lev l (e • w) k = e • lev l w k := fun w => map_nsmul (levH l E n i k) e w
    rw [← key, smul_add, hτ, add_zero, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_smul, Nat.cast_smul_eq_nsmul]

end LateralTheory.KummerTheory
end
end

namespace LateralTheory.Fin.AdicDeg
theorem etale_adic_cohomology_finiteness_holds : LateralTheory.KummerTheory.AdicFin := by
  apply LateralTheory.EWeil.AdicFinPf.AdicFin_of
theorem etale_adic_inverse_limit_comparison_holds : LateralTheory.KummerTheory.AdicLim := by
  apply LateralTheory.KummerTheory.AdicLim_of_fin <;> first | exact etale_adic_cohomology_finiteness_holds
theorem etale_adic_algebraic_comparison_holds : LateralTheory.KummerTheory.AdicAlg := by
  apply LateralTheory.KummerTheory.AdicAlg_of
theorem etale_adic_degree_bound_of_adic_finiteness : LateralTheory.KummerTheory.AdicDeg := by
  apply LateralTheory.KummerTheory.AdicDeg_of <;> first | exact etale_adic_inverse_limit_comparison_holds | exact etale_adic_algebraic_comparison_holds
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.AdicDeg := etale_adic_degree_bound_of_adic_finiteness
end LateralTheory.Fin.AdicDeg
end

section -- merged from Development.EtaleCohomology.KummerTheory.FinLimit
section -- merged from Development.EtaleCohomology.KummerTheory.LimAssemblePf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimRatBij : Prop := ∀ (l : ℕ) [Fact l.Prime] (P Q : Type 1) [AddCommGroup P] [Module ℤ_[l] P] [AddCommGroup Q]
  [Module ℤ_[l] Q] (f : P →ₗ[ℤ_[l]] Q) (N : ℕ), 0 < N → IsoUpTo N f → Function.Bijective (f.baseChange ℚ_[l])

def LimRatAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) →
  Function.Bijective (Φ.baseChange ℚ_[l]) →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

theorem limAssembleCut (h1 : LimRatBij) (h2 : LimRatAssemble) : LimAssemble := by
  intro hA9 l _ X Y S pX pY n i M N r c hnM hN hB e Φ hΦ hiso
  exact h2 hA9 l pX pY n i M r c hnM hB e Φ hΦ (h1 l _ _ Φ N hN hiso)

theorem limRatBij : LimRatBij := by
  intro l _ P Q _ _ _ _ f N hN hiso
  have hPl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hQl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hNS : ((N : ℤ_[l])) ∈ nonZeroDivisors ℤ_[l] :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN.ne')
  have hne : ∀ s ∈ nonZeroDivisors ℤ_[l], algebraMap ℤ_[l] ℚ_[l] s ≠ 0 := fun s hs =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hsm : ∀ {V : Type 1} [AddCommGroup V] [Module ℤ_[l] V] (s : nonZeroDivisors ℤ_[l]) (w : ℚ_[l] ⊗[ℤ_[l]] V),
      s • w = algebraMap ℤ_[l] ℚ_[l] s • w := fun s w => by
    rw [Submonoid.smul_def, algebraMap_smul]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) w
    simp only [TensorProduct.mk_apply] at hs
    have h1 : (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) (f x) = 0 := by
      rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, ← hs, hsm, map_smul, hw, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mp h1
    have h2 : N • ((t : ℤ_[l]) • x) = 0 := hiso.1 _ (by rw [map_smul]; exact ht)
    have h3 : (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) x = 0 := by
      refine (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mpr
        ⟨⟨(N : ℤ_[l]) * t, Submonoid.mul_mem _ hNS t.2⟩, ?_⟩
      rw [Submonoid.mk_smul, mul_smul, Nat.cast_smul_eq_nsmul]; exact h2
    rw [TensorProduct.mk_apply] at h3
    rw [h3, hsm] at hs
    exact (smul_eq_zero.mp hs).resolve_left (hne _ s.2)
  · intro w
    obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) w
    simp only [TensorProduct.mk_apply] at hs
    obtain ⟨x, hx⟩ := hiso.2 z
    have hc := hne _ (Submonoid.mul_mem _ hNS s.2)
    refine ⟨(algebraMap ℤ_[l] ℚ_[l] ((N : ℤ_[l]) * s))⁻¹ • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x), ?_⟩
    rw [map_smul, LinearMap.baseChange_tmul, hx, ← Nat.cast_smul_eq_nsmul ℤ_[l], TensorProduct.tmul_smul, ← hs,
      Submonoid.smul_def, ← mul_smul, ← algebraMap_smul ℚ_[l] ((N : ℤ_[l]) * s) w]
    exact inv_smul_smul₀ hc w

theorem hl_sub (hA9 : A9) (l : ℕ) [Fact l.Prime] (E : Spc) (m j : ℤ) (hm : m < 0) : Subsingleton (Hl l E m j) := by
  constructor
  intro x y
  apply Subtype.ext
  funext k
  exact ((hA9 (ZMod (l ^ k)) (tw (l ^ k) j)).1 E m hm).elim _ _

set_option maxHeartbeats 800000 in
theorem limRatAssemble : LimRatAssemble := by
  intro hA9 l _ X Y S pX pY n i M r c hnM hB e Φ hΦ hbij
  let T := fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0
  let g : ∀ a : ℤ, T a →ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i := fun a =>
    (TensorProduct.lift (e a)).baseChange ℚ_[l] ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[l] ℚ_[l] _ _).symm.toLinearMap
  have hg : ∀ a x y, g a (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) =
      (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
    rw [LinearMap.baseChange_tmul, TensorProduct.lift.tmul, mul_one]
  let κ₀ := DirectSum.toModule ℚ_[l] ℤ _ g
  have hκ₀ : ∀ a x y, κ₀ (DirectSum.lof ℚ_[l] ℤ T a
      (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [κ₀, DirectSum.toModule_lof]
    exact hg a x y
  have hsm : ∀ (a : ℤ) (t : ℤ_[l]) (y : Hl l (sch.obj Y) (n - a) 0) (u : HQ l (sch.obj X) a i),
      u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (t • y)) = algebraMap ℤ_[l] ℚ_[l] t • (u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) := by
    intro a t y u
    rw [← TensorProduct.tmul_smul, TensorProduct.tmul_smul (R := ℤ_[l]), algebraMap_smul]
  let ψ₀ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] ⨁ a : ℤ, T a :=
    { toFun := fun y => ∑ a : Fin (M + 1), ∑ s : Fin (r a), DirectSum.lof ℚ_[l] ℤ T ((a : ℕ) : ℤ)
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c a s) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y a s))
      map_add' := fun y z => by
        simp only [Pi.add_apply, TensorProduct.tmul_add, map_add (f := _), Finset.sum_add_distrib]
      map_smul' := fun t y => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hsm, map_smul, algebraMap_smul] }
  let ψ := ψ₀.liftBaseChange ℚ_[l]
  have key : ∀ u, κ₀ (ψ u) = Φ.baseChange ℚ_[l] u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => rw [map_add (f := _), map_add (f := _), hu, hv, map_add (f := _)]
    | tmul q y =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul]
      change q • κ₀ (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
      rw [hΦ y, TensorProduct.tmul_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, hκ₀, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hsurj : Function.Surjective ψ := by
    intro d
    suffices h : d ∈ LinearMap.range ψ from h
    induction d using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | of a t =>
      change DirectSum.lof ℚ_[l] ℤ T a t ∈ _
      by_cases ha0 : a < 0
      · haveI := hl_sub hA9 l (sch.obj X) a i ha0
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : u = 0 := by
              induction u using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.zero_tmul]
        rw [this, map_zero]; exact Submodule.zero_mem _
      by_cases haM : (M : ℤ) < a
      · haveI := hl_sub hA9 l (sch.obj Y) (n - a) 0 (by omega)
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : v = 0 := by
              induction v using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.tmul_zero]
        rw [this, map_zero]; exact Submodule.zero_mem _
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
      have hm : m < M + 1 := by omega
      have hbase : ∀ (s : Fin (r m)) (q : ℚ_[l]) (y : Hl l (sch.obj Y) (n - (m : ℤ)) 0),
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s) ⊗ₜ[ℚ_[l]] (q ⊗ₜ[ℤ_[l]] y)) ∈
            LinearMap.range ψ := by
        intro s q y
        refine ⟨q ⊗ₜ[ℤ_[l]] (Pi.single (M := fun a : Fin (M + 1) => Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
          ⟨m, hm⟩ (Pi.single s y)), ?_⟩
        rw [LinearMap.liftBaseChange_tmul]
        change q • (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
        rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin (M + 1))]
        · rw [Finset.sum_eq_single s]
          · simp only [Pi.single_eq_same]
            rw [← map_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          · intro s' _ hs'; rw [Pi.single_eq_same, Pi.single_eq_of_ne hs', TensorProduct.tmul_zero,
              TensorProduct.tmul_zero, map_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb]
          simp only [Pi.zero_apply, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hspan := (hB m (by omega)).2
      suffices goal : ∀ t' : HQ l (sch.obj X) (m : ℤ) i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - (m : ℤ)) 0,
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) t' ∈ LinearMap.range ψ from goal t
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add u v hu hv => rw [map_add (f := _)]; exact Submodule.add_mem _ hu hv
      | tmul u v =>
        have hu : u ∈ Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s : HQ l (sch.obj X) (m : ℤ) i)) := by
          rw [hspan]; exact Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨s, rfl⟩ := hu
          induction v using TensorProduct.induction_on with
          | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
          | add v w hv hw => rw [TensorProduct.tmul_add, map_add (f := _)]; exact Submodule.add_mem _ hv hw
          | tmul q y => exact hbase s q y
        | zero => rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [TensorProduct.add_tmul, map_add (f := _)]; exact Submodule.add_mem _ hu hw
        | smul k u _ hu => rw [← TensorProduct.smul_tmul', map_smul]; exact Submodule.smul_mem _ k hu
  have hbijκ : Function.Bijective κ₀ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro d hd
      obtain ⟨u, rfl⟩ := hsurj d
      rw [key] at hd
      have : u = 0 := (injective_iff_map_eq_zero _).mp hbij.1 u hd
      rw [this, map_zero]
    · intro w
      obtain ⟨u, rfl⟩ := hbij.2 w
      exact ⟨ψ u, key u⟩
  exact ⟨LinearEquiv.ofBijective κ₀ hbijκ, fun a x y => hκ₀ a x y⟩

theorem LimAssemble_of : LimAssemble := limAssembleCut limRatBij limRatAssemble

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.LimExtHlPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem lex_red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (Ht.cast hn hi x) = Ht.cast hn hi (red Q q E n i x) := by
  subst hn hi; rfl

theorem lex_cast_add {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    Ht.cast hn hi (x + y) = Ht.cast hn hi x + Ht.cast hn hi y := by
  subst hn hi; rfl

theorem lex_cast_nsmul {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    Ht.cast hn hi (m • x) = m • Ht.cast hn hi x := by
  subst hn hi; rfl

theorem lex_ext_red (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S)
    (a n i : ℤ) (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold ext
  rw [lex_red_cast, (hA Q q hq _).1, pull_red, pull_red]

theorem lex_ext_add_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x x' : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (x + x') y = ext q pX pY a n i x y + ext q pX pY a n i x' y := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), AddMonoidHom.add_apply, lex_cast_add]

theorem lex_ext_add_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht q (sch.obj X) a i) (y y' : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold ext
  rw [map_add (f := _), map_add (f := _), lex_cast_add]

theorem lex_ext_nsmul_left (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i (m • x) y = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, AddMonoidHom.nsmul_apply, lex_cast_nsmul]

theorem lex_ext_nsmul_right (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (m : ℕ)
    (x : Ht q (sch.obj X) a i) (y : Ht q (sch.obj Y) (n - a) 0) :
    ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold ext
  rw [map_nsmul, map_nsmul, lex_cast_nsmul]

def lexF (hA : A11) (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0) : Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => ext (l ^ k) pX pY a n i (lev l x k) (lev l y k), fun k => by
    have : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change red (l ^ (k + 1)) (l ^ k) _ n i (ext (l ^ (k + 1)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))) =
      ext (l ^ k) pX pY a n i (x.1 k) (y.1 k)
    exact (lex_ext_red hA _ _ (pow_dvd_pow l (Nat.le_succ k)) pX pY a n i (x.1 (k + 1)) (y.1 (k + 1))).trans
      (congrArg₂ _ (x.2 k) (y.2 k))⟩

theorem LimExtHl_of : LimExtHl := by
  intro hA l _ X Y S pX pY a n i
  refine ⟨LinearMap.mk₂ ℤ_[l] (lexF hA l pX pY a n i) ?_ ?_ ?_ ?_, fun x y k => ?_⟩
  · intro x x' y
    apply Subtype.ext; funext k
    exact lex_ext_add_left (l ^ k) pX pY a n i (x.1 k) (x'.1 k) (y.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i ((r • x).1 k) (y.1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_left (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · intro x y y'
    apply Subtype.ext; funext k
    exact lex_ext_add_right (l ^ k) pX pY a n i (x.1 k) (y.1 k) (y'.1 k)
  · intro r x y
    apply Subtype.ext; funext k
    change ext (l ^ k) pX pY a n i (x.1 k) ((r • y).1 k) = (r • (lexF hA l pX pY a n i x y).1 k : HtL l k _ n i)
    rw [Submodule.coe_smul, Pi.smul_apply, HtL.smul_eq l k k le_rfl, HtL.smul_eq l k k le_rfl]
    exact lex_ext_nsmul_right (l ^ k) pX pY a n i _ (x.1 k) (y.1 k)
  · rfl

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.LimLHPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LimLHPf

theorem cast_add' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x y : Ht q E n i) :
    (x + y).cast hn hi = x.cast hn hi + y.cast hn hi := by subst hn; subst hi; rfl

theorem cast_nsmul' {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (m : ℕ) (x : Ht q E n i) :
    (m • x).cast hn hi = m • x.cast hn hi := by subst hn; subst hi; rfl

theorem red_cast (Q q : ℕ) {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht Q E n i) :
    red Q q E n' i' (x.cast hn hi) = (red Q q E n i x).cast hn hi := by subst hn; subst hi; rfl

theorem ext_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (y y' : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (y + y') = ext q pX pY a n i x y + ext q pX pY a n i x y' := by
  unfold LateralTheory.KummerTheory.ext; rw [map_add (f := _), map_add (f := _), cast_add']

theorem ext_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ) (x : Ht q (sch.obj X) a i)
    (m : ℕ) (y : Ht q (sch.obj Y) (n - a) 0) : ext q pX pY a n i x (m • y) = m • ext q pX pY a n i x y := by
  unfold LateralTheory.KummerTheory.ext; rw [map_nsmul, map_nsmul, cast_nsmul']

theorem red_ext (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (a n i : ℤ)
    (x : Ht Q (sch.obj X) a i) (y : Ht Q (sch.obj Y) (n - a) 0) :
    red Q q _ n i (ext Q pX pY a n i x y) = ext q pX pY a n i (red Q q _ a i x) (red Q q _ (n - a) 0 y) := by
  unfold LateralTheory.KummerTheory.ext
  rw [red_cast, (hA Q q hq _).1, ← pull_red, ← pull_red]

theorem lh_add (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y y' : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (y + y') = lh q pX pY i r c M n y + lh q pX pY i r c M n y' := by
  unfold LateralTheory.KummerTheory.lh
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_add _ _ _ _ _ _ _ _ _

theorem lh_nsmul (q : ℕ) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i) (M : ℕ) (n : ℤ) (m : ℕ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    lh q pX pY i r c M n (m • y) = m • lh q pX pY i r c M n y := by
  unfold LateralTheory.KummerTheory.lh
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact ext_nsmul _ _ _ _ _ _ _ _ _

theorem red_lh (hA : A11) (Q q : ℕ) [NeZero Q] (hq : q ∣ Q) {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht Q (sch.obj X) a i) (M : ℕ) (n : ℤ)
    (y : ∀ a : Fin (M + 1), Fin (r a) → Ht Q (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    red Q q _ n i (lh Q pX pY i r c M n y) =
      lh q pX pY i r (fun a s => red Q q _ a i (c a s)) M n (fun a s => red Q q _ _ 0 (y a s)) := by
  unfold LateralTheory.KummerTheory.lh
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  exact red_ext hA Q q hq _ _ _ _ _ _ _

theorem lev_red (l : ℕ) [Fact l.Prime] {E : Spc} {n i : ℤ} (x : Hl l E n i) (k : ℕ) :
    red (l ^ (k + 1)) (l ^ k) E n i (lev l x (k + 1)) = lev l x k := x.2 k

instance nz (l : ℕ) [Fact l.Prime] (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

theorem dvd_succ (l k : ℕ) : l ^ k ∣ l ^ (k + 1) := pow_dvd_pow l (Nat.le_succ k)

variable {l : ℕ} [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i)

def phiFun (hA : A11) (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :
    Hl l (sch.obj (pullback pX pY)) n i :=
  ⟨fun k => lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k), fun k => by
    change red (l ^ (k + 1)) (l ^ k) _ n i (lh (l ^ (k + 1)) pX pY i r (fun a s => lev l (c a s) (k + 1)) M n
      (fun a s => lev l (y a s) (k + 1))) = _
    rw [red_lh hA _ _ (dvd_succ l k)]
    simp only [lev_red]⟩

def phi (hA : A11) : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
    Hl l (sch.obj (pullback pX pY)) n i where
  toFun := phiFun pX pY n i M r c hA
  map_add' y y' := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k + lev l (y' a s) k) =
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) +
      lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y' a s) k)
    rw [← lh_add]; rfl)
  map_smul' t y := Subtype.ext (funext fun k => by
    change lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => (t • (show HtL l k _ _ _ from lev l (y a s) k))) =
      (t • (show HtL l k _ _ _ from lev l (phiFun pX pY n i M r c hA y) k))
    have h1 : (fun (a : Fin (M + 1)) (s : Fin (r a)) =>
        (t • (show HtL l k (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0 from lev l (y a s) k) : Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)) =
        (PadicInt.toZModPow k t).val • (fun (a : Fin (M + 1)) (s : Fin (r a)) => lev l (y a s) k) :=
      funext fun a => funext fun s => HtL.smul_eq l k k le_rfl _ _ _ t _
    rw [h1, lh_nsmul]
    exact (HtL.smul_eq l k k le_rfl _ _ _ t _).symm)

theorem phi_ker (hA : A11) (N : ℕ)
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (y : ∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
    (hy : phi pX pY n i M r c hA y = 0) : N • y = 0 := by
  funext a s
  apply Subtype.ext; funext k
  have h0 : lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n (fun a s => lev l (y a s) k) = 0 := by
    have := congrArg (fun z : Hl l (sch.obj (pullback pX pY)) n i => lev l z k) hy
    exact this
  have := congrFun (congrFun ((hiso k).1 _ h0) a) s
  exact this

theorem phi_coker (hA : A11) (N : ℕ)
    (hfin : ∀ (k : ℕ) (m : ℤ), Finite (Ht (l ^ k) (sch.obj Y) m 0))
    (hiso : ∀ k, IsoUpTo N (lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n))
    (b : Hl l (sch.obj (pullback pX pY)) n i) : ∃ y, phi pX pY n i M r c hA y = N • b := by
  let D : ℕ → Type 1 := fun k => ∀ a : Fin (M + 1), Fin (r a) → Ht (l ^ k) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0
  let Sl : ℕ → Type 1 := fun k => {z : D k // lh (l ^ k) pX pY i r (fun a s => lev l (c a s) k) M n z = N • lev l b k}
  let f : ∀ k, Sl (k + 1) ⟶ Sl k := fun k => TypeCat.ofHom fun (z : Sl (k + 1)) => (⟨fun a s => red (l ^ (k + 1)) (l ^ k) _ _ 0 (z.1 a s), by
    have h := congrArg (red (l ^ (k + 1)) (l ^ k) _ n i) z.2
    rw [red_lh hA _ _ (dvd_succ l k), map_nsmul, lev_red] at h
    simp only [lev_red] at h
    exact h⟩ : Sl k)
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence f
  have : ∀ j, Finite (F.obj j) := fun j => by
    have := hfin (unop j)
    change Finite (Sl (unop j))
    have : ∀ (a : Fin (M + 1)), Finite (Fin (r a) → Ht (l ^ unop j) (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) :=
      fun a => by have := hfin (unop j) (n - ((a : ℕ) : ℤ)); infer_instance
    have : Finite (D (unop j)) := Pi.finite
    exact Subtype.finite
  have : ∀ j, Nonempty (F.obj j) := fun j => by
    obtain ⟨z, hz⟩ := (hiso (unop j)).2 (lev l b (unop j))
    exact ⟨(⟨z, hz⟩ : Sl (unop j))⟩
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  have hstep : ∀ k a s, red (l ^ (k + 1)) (l ^ k) _ _ 0 (((sec (op (k + 1)) : Sl (k + 1)).1) a s) =
      ((sec (op k) : Sl k).1) a s := by
    intro k a s
    have h := hsec (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at h
    exact congrArg (fun z : Sl k => z.1 a s) h
  refine ⟨fun a s => ⟨fun k => ((sec (op k) : Sl k).1) a s, fun k => hstep k a s⟩, ?_⟩
  apply Subtype.ext; funext k
  exact (sec (op k) : Sl k).2

theorem LimLH_of : LimLH := by
  intro hA l _ X Y S pX pY n i M N r c hfin hiso
  exact ⟨phi pX pY n i M r c hA, fun y k => rfl,
    fun y hy => phi_ker pX pY n i M r c hA N hiso y hy, fun b => phi_coker pX pY n i M r c hA N hfin hiso b⟩

end LateralTheory.KummerTheory.LimLHPf
end
end

namespace LateralTheory.Fin.Limit
theorem etale_limit_extension_groups_henselian_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimExtHl := by
  apply LateralTheory.KummerTheory.LimExtHl_of
theorem etale_limit_local_homotopy_compatible_in_inverse_limits_assembly : LateralTheory.KummerTheory.LimLH := by
  apply LateralTheory.KummerTheory.LimLHPf.LimLH_of
theorem etale_limit_cohomology_assembled_from_stages : LateralTheory.KummerTheory.LimAssemble := by
  apply LateralTheory.KummerTheory.LimAssemble_of
theorem etale_cohomology_commutes_with_inverse_limits : LateralTheory.KummerTheory.Limit := by
  apply LateralTheory.KummerTheory.Limit_of <;> first | exact etale_limit_extension_groups_henselian_in_inverse_limits_assembly | exact etale_limit_local_homotopy_compatible_in_inverse_limits_assembly | exact etale_limit_cohomology_assembled_from_stages
theorem intersectionNumber_baseChange : LateralTheory.KummerTheory.Limit := etale_cohomology_commutes_with_inverse_limits
end LateralTheory.Fin.Limit
end

section -- merged from Development.EtaleCohomology.KummerTheory.InvOfField
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory

theorem IsoUpTo.comb_mono {q : ℕ} {E : Spc} {n i : ℤ} {r : ℕ} {c : Fin r → Ht q E n i} {N N' : ℕ} (hd : N ∣ N')
    (h : IsoUpTo N (comb q c)) : IsoUpTo N' (comb q c) := by
  obtain ⟨m, rfl⟩ := hd
  refine ⟨fun a ha => by rw [mul_comm, mul_smul, h.1 a ha, smul_zero], fun b => ?_⟩
  obtain ⟨a, ha⟩ := h.2 (m • b)
  exact ⟨a, by rw [ha, mul_smul]⟩

theorem inv_of_field (l : ℕ) (k : Type) [Field k] (hl : IsUnit (l : k)) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) : Inv l (sch.obj X) := by
  intro U ⟨x⟩
  have h := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ((show U ⟶ X from x) ≫ p).appTop).hom
  rwa [map_natCast] at h

theorem goal_of (hLH : LH) (hInv : SHInv) (hSt : Stalk) (hB : Bock) (hAd : AdicDeg) (hL : Limit) : GOAL := by
  intro a2 a6n a6r a7 a8 a9 a10 a11 b1 b2 b3 e2 e3 e4 l _ k _ _ hl X Y pX pY _ _ _ n i
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hu : ∀ j : ℕ, IsUnit ((l ^ j : ℕ) : k) := fun j => by rw [Nat.cast_pow]; exact hl.pow j
  have hA := hAd a11 l (sch.obj X) i (fun b => hB a7 a8 a10 a11 l b _ i (inv_of_field l k hl pX))
    (fun j m => e4 (l ^ j) k (hu j) pX m i)
  choose r c N hN hQ hI using hA
  obtain ⟨e, he⟩ := hLH a2 a6n b1
  let M : ℕ := n.toNat + 1
  let N' : ℕ := ∏ a ∈ Finset.range (M + 1), N (a : ℕ)
  have hN' : 0 < N' := Finset.prod_pos fun a _ => hN _
  refine hL a9 a11 l pX pY n i M (N' ^ e M) (fun a => r a) (fun a => c a) (by omega) (pow_pos hN' _) (fun a _ => hQ _)
    (fun j m => e4 (l ^ j) k (hu j) pY m 0) fun j => ?_
  refine he (l ^ j) pX (hu j) i _ _ M N' (fun A s hA m hm => ?_) pY n (by omega)
  exact hSt a6n a6r a9 b2 (l ^ j) pX A s hA (hu j) i _ _ M N' (hInv a9 b2 b3 e2 e3 (l ^ j) k (hu j) pX A s hA i)
    (fun a ha => (hI a j).comb_mono (Finset.dvd_prod_of_mem _ (Finset.mem_range.2 (by omega)))) m hm

end LateralTheory.KummerTheory

end
end

namespace LateralTheory.KummerTheory

theorem goal_holds : GOAL :=
  goal_of LateralTheory.Fin.LH.intersectionNumber_baseChange LateralTheory.Fin.SHInv.intersectionNumber_baseChange LateralTheory.Fin.Stalk.intersectionNumber_baseChange LateralTheory.Fin.Bock.intersectionNumber_baseChange
    LateralTheory.Fin.AdicDeg.intersectionNumber_baseChange LateralTheory.Fin.Limit.intersectionNumber_baseChange

end LateralTheory.KummerTheory
