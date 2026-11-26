module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBound
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH
namespace MinorTest

theorem exists_norm_between {C : Type*} [NontriviallyNormedField C] [IsAlgClosed C] {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) : ∃ x : C, a < ‖x‖ ∧ ‖x‖ < b := by
  have hb : 0 < b := ha.trans_lt hab
  have hr : a / b < 1 := (div_lt_one hb).2 hab
  have hr0 : 0 ≤ a / b := div_nonneg ha hb.le
  obtain ⟨z, hz1, hz2⟩ : ∃ z : C, a / b < ‖z‖ ∧ ‖z‖ < 1 := by
    obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one C
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr).eventually_lt_const hy0
    obtain ⟨n, hn, hn1⟩ := (h.and (Filter.eventually_gt_atTop 0)).exists
    obtain ⟨x, rfl⟩ := IsAlgClosed.exists_pow_nat_eq y hn1
    rw [norm_pow] at hn hy1
    exact ⟨x, lt_of_pow_lt_pow_left₀ n (norm_nonneg x) hn,
      (pow_lt_one_iff_of_nonneg (norm_nonneg x) hn1.ne').1 hy1⟩
  have hz0 : 0 < ‖z‖ := hr0.trans_lt hz1
  have hy : 1 < ‖z‖⁻¹ := (one_lt_inv₀ hz0).2 hz2
  obtain ⟨n, h1, h2⟩ := exists_mem_Ioc_zpow hb hy
  refine ⟨z⁻¹ ^ n, ?_, ?_⟩
  · rw [norm_zpow, norm_inv]
    rw [zpow_add_one₀ (inv_pos.2 hz0).ne', ← div_eq_mul_inv, le_div_iff₀ hz0] at h2
    rw [div_lt_iff₀ hb, mul_comm] at hz1
    exact hz1.trans_le h2
  · rwa [norm_zpow, norm_inv]

theorem norm_det_le_pow {C J : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J] [DecidableEq J]
    (A : Matrix J J C) {ρ : ℝ} (hρ : 0 ≤ ρ) (h : ∀ i j, ‖A i j‖ ≤ ρ) :
    ‖A.det‖ ≤ ρ ^ Fintype.card J := by
  rw [Matrix.det_apply']
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun σ _ => ?_
  have hs : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : C)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [norm_mul, hs, _root_.one_mul, norm_prod, ← Finset.card_univ, ← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun i _ => h _ _

theorem norm_det_le_of_comb {C J I : Type*} [NormedField C] [IsUltrametricDist C] [Fintype J]
    [DecidableEq J] [Fintype I] (g : I → J → C) (c : J → I → C) (hc : ∀ i m, ‖c i m‖ ≤ 1) {ν : ℝ}
    (hν : 0 ≤ ν) (h : ∀ k : J → I, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν) :
    ‖Matrix.det (Matrix.of fun i => ∑ m, c i m • g m)‖ ≤ ν := by
  have e : Matrix.det (Matrix.of fun i => ∑ m, c i m • g m) =
      ∑ k : J → I, (∏ i, c i (k i)) • Matrix.det (Matrix.of fun i j => g (k i) j) := by
    have := (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_sum
      (fun i m => c i m • g m)
    refine this.trans (Finset.sum_congr rfl fun k _ => ?_)
    exact (Matrix.detRowAlternating (n := J) (R := C)).toMultilinearMap.map_smul_univ
      (fun i => c i (k i)) (fun i => g (k i))
  rw [e]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hν fun k _ => ?_
  rw [smul_eq_mul, norm_mul, norm_prod]
  calc _ ≤ 1 * ν := mul_le_mul (Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hc _ _) (h k)
        (norm_nonneg _) zero_le_one
    _ = ν := _root_.one_mul _

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (h : Filter.Tendsto q Filter.cofinite Filter.atTop) {x : X} (hx0 : x ≠ 0) : 0 < q x := by
  by_contra hx
  push_neg at hx
  have hfin : {v | ¬ (0 : ℝ) < q v}.Finite := Filter.eventually_cofinite.1 (h.eventually_gt_atTop 0)
  have hinj : Function.Injective fun n : ℕ => ((n : ℤ) + 1) • x := by
    intro a b hab
    have := smul_left_injective ℤ hx0 hab
    omega
  refine Set.infinite_of_injective_forall_mem hinj (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  refine mul_nonpos_of_nonneg_of_nonpos ?_ hx
  positivity

theorem exists_eStd_eq (g n : ℕ) (φ : (Fin g ⊕ Fin g → ZMod n) →+ ZMod n) :
    ∃ a, ∀ b, eStd g n a b = φ b := by
  let ψ : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n := φ.toZModLinearMap n
  refine ⟨Sum.elim (fun i => φ (Pi.single (.inr i) 1)) (fun i => -φ (Pi.single (.inl i) 1)), fun b => ?_⟩
  have hb : φ b = ∑ s, b s * φ (Pi.single s 1) := by
    change ψ b = ∑ s, b s * ψ (Pi.single s 1)
    conv_lhs => rw [pi_eq_sum_univ' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul]
  rw [hb, Fintype.sum_sum_type, ← Finset.sum_add_distrib, eStd]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

theorem subsingleton_of_perp_eq_bot (τ : S.Test p y₀) (h : S.perp τ.yy.ker = ⊥) (x : τ.X) : x = 0 := by
  have h2 : 2 ≤ S.r * S.N := le_trans S.N_ge (Nat.le_mul_of_pos_left _ S.r_pos)
  haveI : Fact (1 < S.r * S.N) := ⟨h2⟩
  let b := Module.Free.chooseBasis ℤ τ.X
  haveI : IsEmpty (Module.Free.ChooseBasisIndex ℤ τ.X) := by
    refine ⟨fun i => ?_⟩
    let f : τ.X →+ ZMod (S.r * S.N) := (Int.castAddHom _).comp (b.coord i).toAddMonoidHom
    let f' : τ.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : τ.X →+ τ.X).range →+ ZMod (S.r * S.N) :=
      QuotientAddGroup.lift _ f (by
        rintro _ ⟨v, rfl⟩
        rw [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply, map_nsmul, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul])
    obtain ⟨a, ha⟩ := exists_eStd_eq _ _ (f'.comp τ.yy)
    have hm : a ∈ S.perp τ.yy.ker := fun u hu => by
      rw [ha, AddMonoidHom.comp_apply, (AddMonoidHom.mem_ker).1 hu, map_zero]
    rw [h, AddSubgroup.mem_bot] at hm
    obtain ⟨u, hu⟩ := τ.yy_onto (QuotientAddGroup.mk (b i))
    have := ha u
    rw [hm, AddMonoidHom.comp_apply, hu] at this
    simp [eStd, f', f] at this
  exact b.repr.injective (Subsingleton.elim _ _)

theorem eq_bot_of_char {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (h : ∀ c : T →+ ZMod S.N, c = 0) :
    T = ⊥ := by
  obtain ⟨-, d, ⟨e⟩⟩ := hT
  haveI : Fact (1 < S.N) := ⟨S.N_ge⟩
  haveI : IsEmpty (Fin d) := by
    refine ⟨fun i => ?_⟩
    have := DFunLike.congr_fun (h ((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
      ((Pi.evalAddMonoidHom (fun _ : Fin d => ZMod (S.r * S.N)) i).comp e.toAddMonoidHom)))
      (e.symm (fun _ => 1))
    simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe,
      AddEquiv.apply_symm_apply, Pi.evalAddMonoidHom_apply, RingHom.toAddMonoidHom_eq_coe, map_one,
      AddMonoidHom.zero_apply] at this
    exact one_ne_zero this
  rw [eq_bot_iff]
  intro t ht
  have : (⟨t, ht⟩ : T) = 0 := e.injective (Subsingleton.elim _ _)
  exact congrArg Subtype.val this

end MinorTest

open MinorTest in
theorem minors_dual_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  intro o Ω _ _ _ _ S p _ y₀ τ hint _ n ρ₀ g hρ hg
  obtain ⟨B, l, α, -, hdet, -, hl, hall, -, hE⟩ := exists_adapted_basis_testLattice o Ω S p y₀ τ hint
  have hN : (0 : ℝ) < S.N := by exact_mod_cast lt_of_lt_of_le two_pos S.N_ge
  have hq : ∀ x, 0 ≤ τ.q x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (pos_of_tendsto τ.q τ.pos hx).le
  have hl1 : ∀ i, 1 ≤ ‖l i‖ := fun i => by
    rw [hl]; exact Real.one_le_exp (div_nonneg (hq _) hN.le)
  set M : Matrix S.J S.J (PadicAlgCl p) := Matrix.of fun i j => l i * B i j with hM
  have hMdet : ‖M.det‖ = ∏ i, ‖l i‖ := by
    rw [hM, Matrix.det_mul_column, norm_mul, hdet, _root_.mul_one, norm_prod]
  have hM1 : 1 ≤ ‖M.det‖ := by
    rw [hMdet]; exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
  have key : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ * ‖M.det‖ ≤ ρ₀ ^ Fintype.card S.J := fun k => by
    rw [← Matrix.det_transpose M, ← norm_mul, ← Matrix.det_mul]
    refine norm_det_le_pow _ hρ.le fun i j => ?_
    exact (hg (g (k i))).1 (Submodule.subset_span ⟨_, rfl⟩) (fun t => l j * B j t)
      (hE ▸ Submodule.subset_span ⟨j, rfl⟩)
  have h1 : ∀ k : S.J → Fin n,
      ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J := fun k =>
    (le_mul_of_one_le_right (norm_nonneg _) hM1).trans (key k)
  have hρd : 0 < ρ₀ ^ Fintype.card S.J := pow_pos hρ _
  refine ⟨h1, ⟨?_, fun hbot => ?_⟩⟩
  · rintro ⟨k, hk⟩
    have h2 := key k
    rw [hk, mul_le_iff_le_one_right hρd, hMdet] at h2
    refine eq_bot_of_char τ.isoFree fun c => ?_
    obtain ⟨i, rfl⟩ := hall c
    have h3 : ‖l i‖ ≤ 1 := by
      refine le_trans ?_ h2
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      refine le_mul_of_one_le_right (norm_nonneg _) ?_
      exact Finset.prod_induction _ (1 ≤ ·) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun i _ => hl1 i
    have h4 : α i = 0 := by
      by_contra hne
      have := Real.one_lt_exp_iff.2 (div_pos (pos_of_tendsto τ.q τ.pos hne) hN)
      rw [hl] at h3
      linarith
    rw [h4, map_zero]
  · have hMe : ‖M.det‖ = 1 := by
      rw [hMdet]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hl, subsingleton_of_perp_eq_bot τ hbot (α i)]
      simp
    have hMu : IsUnit M.det := by
      rw [isUnit_iff_ne_zero, ← norm_ne_zero_iff, hMe]; exact one_ne_zero
    by_contra hne
    push_neg at hne
    obtain ⟨ν, hν0, hν1, hν2⟩ : ∃ ν : ℝ, 0 ≤ ν ∧ ν < ρ₀ ^ Fintype.card S.J ∧
        ∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ν := by
      rcases isEmpty_or_nonempty (S.J → Fin n) with he | he
      · exact ⟨0, le_rfl, hρd, fun k => he.elim k⟩
      · obtain ⟨k₀, hk₀⟩ := Finite.exists_max
          fun k : S.J → Fin n => ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖
        exact ⟨_, norm_nonneg _, lt_of_le_of_ne (h1 k₀) (hne k₀), hk₀⟩
    obtain ⟨x, hx1, hx2⟩ := exists_norm_between (C := PadicAlgCl p) hν0 hν1
    obtain ⟨z, rfl⟩ := IsAlgClosed.exists_pow_nat_eq x (Fintype.card_pos (α := S.J))
    have hz : ‖z‖ ≤ ρ₀ := by
      rw [norm_pow] at hx2
      exact (lt_of_pow_lt_pow_left₀ _ hρ.le hx2).le
    set W : Matrix S.J S.J (PadicAlgCl p) := z • (M.transpose)⁻¹ with hW
    have hWM : W * M.transpose = z • (1 : Matrix S.J S.J (PadicAlgCl p)) := by
      rw [hW, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (by rwa [Matrix.det_transpose])]
    have hWdet : ‖W.det‖ = ‖z ^ Fintype.card S.J‖ := by
      have := congrArg (fun A => ‖Matrix.det A‖) hWM
      simpa only [Matrix.det_mul, Matrix.det_transpose, norm_mul, hMe, _root_.mul_one, Matrix.det_smul,
        Matrix.det_one] using this
    have hmem : ∀ i, W i ∈ Submodule.span (OO p) (Set.range g) := fun i => by
      rw [hg, hE]
      intro v hv
      induction hv using Submodule.span_induction with
      | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        have : W i ⬝ᵥ (fun t => l j * B j t) = (W * M.transpose) i j := rfl
        rw [this, hWM, Matrix.smul_apply, Matrix.one_apply]
        split_ifs
        · simpa using hz
        · simpa using hρ.le
      | zero => simpa using hρ.le
      | add u v _ _ hu hv =>
        rw [dotProduct_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
      | smul a v _ hv =>
        have : a • v = (a : PadicAlgCl p) • v := rfl
        rw [this, dotProduct_smul, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) ((mem_OO_iff _).1 a.2)).trans hv
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (hmem i)
    have h5 := norm_det_le_of_comb g (fun i m => (c i m : PadicAlgCl p))
      (fun i m => (mem_OO_iff _).1 (c i m).2) hν0 hν2
    have h6 : (Matrix.of fun i => ∑ m, (c i m : PadicAlgCl p) • g m) = W := by
      ext i j
      exact congrFun (hc i) j
    rw [h6, hWdet] at h5
    linarith
end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MaximalMinorsDualThetaTestLatticeBoundStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
theorem _root_.GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → ∀ (n : ℕ) (ρ₀ : ℝ) (g : Fin n → S.J → PadicAlgCl p), 0 < ρ₀ → (∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range g) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ ρ₀) → (∀ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ ≤ ρ₀ ^ Fintype.card S.J) ∧ ((∃ k : S.J → Fin n, ‖Matrix.det (Matrix.of fun i j => g (k i) j)‖ = ρ₀ ^ Fintype.card S.J) ↔ S.perp τ.yy.ker = ⊥) := by
  first | exact @GlobalTheory.ZH.minors_dual_testLattice | exact GlobalTheory.ZH.minors_dual_testLattice | (intros; apply GlobalTheory.ZH.minors_dual_testLattice <;> assumption)
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem RatModel.exists_ringHom_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    {K : Type} [Field K] (y : Sp K ⟶ M.Z) {U : Set M.Z} (hy : Set.range y ⊆ U) :
    ∃ ψ : M.ringOn U →+* K, ∀ a, ψ a = M.val y a :=
  ⟨(RatModel.valHom y _ (RatModel.range_eq_singleton y (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (RatModel.ringOn_le_O (hy ⟨_, rfl⟩))).toRingHom, fun _ => rfl⟩

theorem minors_regular_and_unit_iff : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (R' : Subalgebra o Ω) (hR : S.R ≤ R') (n a : ℕ) (GG : Fin n → S.J → R'), S.Over₀ M U₀ → R' ≤ M.ringOn U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y' : R' →+* PadicAlgCl p) (τ : S.Test p (y'.comp (Subalgebra.inclusion hR).toRingHom)), (∀ b : o, ‖y' (algebraMap o R' b)‖ ≤ 1) → ∀ w : S.J → PadicAlgCl p, w ∈ Submodule.span (OO p) (Set.range fun k j => y' (GG k j)) ↔ ∀ v ∈ τ.E, ‖w ⬝ᵥ v‖ ≤ τ.δ ^ a) → ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (∀ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k / S.th x₀ ^ (a * Fintype.card S.J) ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ≠ 0 ∧ S.th x₀ ^ (a * Fintype.card S.J) / (fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω))) k ∈ M.O z) := by
  intro o Ω _ _ _ _ S M U₀ R' hR n a GG hO hR' hLL hT hsup hTT hcl hGG
  obtain ⟨hLL, -⟩ := hLL
  obtain ⟨-, -, -, hcp⟩ := hTT
  set D : (S.J → Fin n) → Ω := fun k : S.J → Fin n => Matrix.det (Matrix.of fun i j => (GG (k i) j : Ω)) with hD
  set m := a * Fintype.card S.J with hm

  have hDR : ∀ k, D k = ((Matrix.det (Matrix.of fun i j => GG (k i) j) : R') : Ω) := fun k =>
    ((R'.val.toRingHom.map_det (Matrix.of fun i j => GG (k i) j))).symm
  have hclosed : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → ∀ x₀ ∈ S.supI M z,
      (∀ k, D k / S.th x₀ ^ m ∈ M.O z) ∧ (S.TT M z = ⊥ ↔ ∃ k, D k ≠ 0 ∧ S.th x₀ ^ m / D k ∈ M.O z) := by
    intro z hz x₀ hx₀
    have h0 : S.th x₀ ≠ 0 := hx₀.1
    have hth : S.th x₀ ∈ M.ringOn U₀ := hO.le (S.th_mem x₀)
    have hinv : (S.th x₀)⁻¹ ∈ M.ringOn U₀ := hO.th_unit x₀ h0
    have hDm : ∀ k, D k ∈ M.ringOn U₀ := fun k => hDR k ▸ hR' (Subtype.prop _)
    have hφ : ∀ k, D k / S.th x₀ ^ m ∈ M.ringOn U₀ := fun k => by
      rw [div_eq_mul_inv, ← inv_pow]
      exact mul_mem (hDm k) (pow_mem hinv m)
    have htest : ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y →
        (∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ ≤ 1) ∧
        ((∃ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ = 1) ↔ S.TT M z = ⊥) := by
      intro p _ y hy
      obtain ⟨ψ, hψ⟩ := M.exists_ringHom_val (gPt p ≫ y) hy.2
      obtain ⟨y₀, hAt, hb, ⟨τ⟩⟩ := hT z p y hy
      let y' : R' →+* PadicAlgCl p := ψ.comp (Subalgebra.inclusion hR').toRingHom
      have e : y₀ = y'.comp (Subalgebra.inclusion hR).toRingHom :=
        RingHom.ext fun b => (hAt b).trans (hψ ⟨b, hO.le b.2⟩).symm
      subst e
      obtain ⟨hs, hH⟩ := hsup z p y _ τ hy hAt
      have hδ := (hs x₀).1 hx₀
      have hpos := τ.δ_pos
      obtain ⟨h1, h2⟩ := GlobalTheory.T.maximal_minors_dual_thetaTest_lattice_bound o Ω S p _ τ hb hcl n (τ.δ ^ a) (fun k j => y' (GG k j)) (pow_pos hpos a)
        (hGG p y' τ hb)
      rw [← pow_mul, ← hm] at h1 h2
      have hpm : 0 < τ.δ ^ m := pow_pos hpos m
      have hval : ∀ k, ‖M.val (gPt p ≫ y) (D k / S.th x₀ ^ m)‖ * τ.δ ^ m =
          ‖Matrix.det (Matrix.of fun i j => y' (GG (k i) j))‖ := by
        intro k
        have e1 : (⟨_, hφ k⟩ : M.ringOn U₀) * ⟨_, hth⟩ ^ m =
            Subalgebra.inclusion hR' (Matrix.det (Matrix.of fun i j => GG (k i) j)) :=
          Subtype.ext ((div_mul_cancel₀ _ (pow_ne_zero m h0)).trans (hDR k))
        have e2 := congrArg (fun t => ‖ψ t‖) e1
        simp only [map_mul, map_pow, norm_mul, norm_pow] at e2
        rw [hψ, hψ] at e2
        rw [← hδ]
        refine e2.trans ?_
        exact congrArg norm (y'.map_det (Matrix.of fun i j => GG (k i) j))
      refine ⟨fun k => ?_, ?_⟩
      · have := h1 k
        rw [← hval] at this
        exact le_of_mul_le_mul_right (by simpa using this) hpm
      · rw [ThetaSys.TT, hH, ← h2]
        refine exists_congr fun k => ?_
        rw [← hval]
        exact ⟨fun h => by rw [h, _root_.one_mul], fun h => mul_right_cancel₀ hpm.ne' (h.trans (_root_.one_mul _).symm)⟩
    obtain ⟨⟨p, _, y, hy⟩, hreg⟩ := hLL U₀ le_rfl hO.ne z hz
    have hmem : ∀ k, D k / S.th x₀ ^ m ∈ M.O z := fun k =>
      hreg _ (hφ k) fun p _ y hy => (htest p y hy).1 k
    refine ⟨hmem, ?_⟩
    rw [← (htest p y hy).2]
    refine exists_congr fun k => ?_
    rw [RatModel.norm_val_eq_one_iff hy.1 (hmem k), RatModel.isUnit_O_iff]
    simp only [inv_div, ne_eq, div_eq_zero_iff, pow_ne_zero m h0, or_false]
  intro z x₀ hx₀
  have hTTeq : ∀ x : M.Z, S.supI M x = S.supI M z → S.TT M x = S.TT M z := fun x h => by
    rw [ThetaSys.TT, ThetaSys.TT, ThetaSys.HH, ThetaSys.HH, h]
  obtain ⟨x, -, hx, hzx, hs⟩ := hcp z ⊤ trivial
  obtain ⟨h1, h2⟩ := hclosed x hx x₀ (hs ▸ hx₀)
  refine ⟨fun k => RatModel.O_le_of_specializes hzx (h1 k), fun h => ?_, fun ⟨k, hk, hk'⟩ => ?_⟩
  · obtain ⟨k, hk, hk'⟩ := h2.1 ((hTTeq x hs).trans h)
    exact ⟨k, hk, RatModel.O_le_of_specializes hzx hk'⟩
  · obtain ⟨x', hW, hx', -, hs'⟩ := hcp z ⟨_, M.isOpen_setOf_mem_O (S.th x₀ ^ m / D k)⟩ hk'
    exact (hTTeq x' hs').symm.trans ((hclosed x' hx' x₀ (hs' ▸ hx₀)).2.2 ⟨k, hk, hW⟩)

end GlobalTheory.ZH
