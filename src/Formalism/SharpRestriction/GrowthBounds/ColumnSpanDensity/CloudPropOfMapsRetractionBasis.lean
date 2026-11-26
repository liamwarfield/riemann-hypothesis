module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudBoundOfPropAndWeylDimension
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InvariantSectionsTransportGL
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorizationBoundMonoLattices
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.CloudCount
section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.FactorsLEOfFintype
section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.NLeDAll
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

theorem nLeD_all {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c)
    (hfac : ∀ e, IsEdge p n' 1 e →
      FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 := by
  classical
  have hcnt := restEdgeCountSrc
  have hdnn := dL_nonneg R lam0
  by_cases hn0 : n = 0
  · subst hn0; simpa using hdnn
  have hL : IsLattice R.W (colSpan R.W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq)) := ⟨1, by simp, rfl⟩
  obtain ⟨Ne, es, hinj, hes, hNe⟩ := hcnt p n' R (m + 1) (by omega) _ hL
  have hc1 : 1 ≤ c := by
    have : (0 : ℝ) < c := by linarith
    exact_mod_cast this
  have hdata : ∀ i : Fin Ne, ∃ (x : Fin n → Vsp R.Kf lam0)
      (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z z' : R.O), z ≠ 0 ∧
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ Re' p R.ι R.σ R.w 1 lam0 (es i)) ∧
      z' * z = R.w ^ (c - 1) ∧
      ∀ a b, be p 1 lam0 (x a) (y b) = if a = b then algebraMap R.O R.Kf z else 0 := by
    intro i
    rcases hfac (es i) (hes i).1 with h0 | ⟨x, y, hx, hy, z, Mx, hz, hv, hM⟩
    · exact absurd h0 hn0
    · obtain ⟨z', hz'⟩ := dvd_w_pow_of_vLEO R.std.2.1 R.std.1.w_sq hz hDc hv
      refine ⟨x, fun b => ∑ l, Mx l b • y l, z, z', hz, hx,
        fun b => Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (hy l)), by rw [hz']; ring, fun a b => ?_⟩
      rw [be_sum]
      exact hM a b
  choose x y z z' hz0 hx hy hzz hxy using hdata
  have hβ : ∀ i l : Fin Ne × Fin n, ∃ β : R.O, β ∈ IsLocalRing.maximalIdeal R.O ∧
      be p 1 lam0 (x i.1 i.2) (y l.1 l.2) =
        algebraMap R.O R.Kf (((1 : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O) i l + β) * z l.1) := by
    rintro ⟨i, a⟩ ⟨l, b⟩
    by_cases hil : i = l
    · subst hil
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      simp only
      rw [hxy, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp
      · have : ((i, a) : Fin Ne × Fin n) ≠ (i, b) := fun h => hab (Prod.mk.inj h).2
        rw [if_neg hab, if_neg this]; simp
    · have hne : es l ≠ es i := fun h => hil (hinj h).symm
      have hXs := CCL_other R lam0 t c (es i) (es l) (hes _).1 ((hes _).2.trans (hes _).2.symm) hne (hx i a)
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b)
      have h2 : ((i, a) : Fin Ne × Fin n) ≠ (l, b) := fun h => hil (Prod.mk.inj h).1
      refine ⟨R.w * b' * z' l, Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ R.w_mem), ?_⟩
      simp only
      rw [hb, Matrix.one_apply_ne h2, zero_add]
      congr 1
      have h3 : R.w ^ c = R.w * R.w ^ (c - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [h3, ← hzz l]
      ring
  choose β hβm hβe using hβ
  let P : Matrix (Fin Ne × Fin n) (Fin Ne × Fin n) R.O := Matrix.of fun i l => (1 : Matrix _ _ R.O) i l + β i l
  have hP : IsUnit P.det := by
    apply isUnit_det_of_one_add'
    intro i l
    simpa [P] using hβm i l
  have hinjK : Function.Injective (algebraMap R.O R.Kf) := by
    have hfr : IsFractionRing R.O R.Kf := R.std.1.frac_O
    exact IsFractionRing.injective R.O R.Kf
  have hPK : ((algebraMap R.O R.Kf).mapMatrix P).det ≠ 0 := by
    rw [← RingHom.map_det]
    intro h0
    have : P.det = 0 := hinjK (by rw [h0, map_zero])
    rw [this] at hP
    exact not_isUnit_zero hP
  have hli : LinearIndependent R.Kf (fun i : Fin Ne × Fin n => x i.1 i.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h1 : ∀ l : Fin Ne × Fin n, ∑ i, g i * algebraMap R.O R.Kf (P i l) = 0 := by
      intro l
      have h2 : be p 1 lam0 (∑ i, g i • x i.1 i.2) (y l.1 l.2) = 0 := by
        rw [hg]; simp [be]
      rw [be_sum_left] at h2
      have h3 : (∑ i, g i * algebraMap R.O R.Kf (P i l)) * algebraMap R.O R.Kf (z l.1) = 0 := by
        rw [← h2, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hβe i l, map_mul, mul_assoc]
        rfl
      have hz : algebraMap R.O R.Kf (z l.1) ≠ 0 := fun h => hz0 l.1 (hinjK (by rw [h, map_zero]))
      exact (mul_eq_zero.1 h3).resolve_right hz
    have h4 : Matrix.vecMul g ((algebraMap R.O R.Kf).mapMatrix P) = 0 := by
      funext l
      simpa [Matrix.vecMul, dotProduct] using h1 l
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero hPK h4
    intro i
    rw [h5]; rfl
  have hpos : 0 < dimV R.Kf lam0 := Formalism.MainNotions.G.LatticeSystems.kp_dimV_pos R.Kf lam0 hDom
  have hfin : Module.Finite R.Kf (Vsp R.Kf lam0) := Module.finite_of_finrank_pos hpos
  have hcard : Ne * n ≤ dimV R.Kf lam0 := by
    have := hli.fintype_card_le_finrank
    simpa [dimV] using this
  have hNpos := gaussianNumber_prime_pow_pos R (m + 1) (by omega)
  unfold dL
  rw [le_div_iff₀ hNpos]
  have h6 : ((Ne * n : ℕ) : ℝ) ≤ (dimV R.Kf lam0 : ℝ) := by exact_mod_cast hcard
  have h7 : (n : ℝ) * gaussianNumber (p ^ n') (m + 1) ≤ (n : ℝ) * Ne := mul_le_mul_of_nonneg_left hNe (Nat.cast_nonneg _)
  push_cast at h6
  linarith

theorem nEdge {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (e e' : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (he' : IsEdge p n' 1 e')
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e') (Re' p R.ι R.σ R.w 1 lam0 e') n D := by
  classical
  have hFun := restFunct
  have hfrW : IsFractionRing R.W R.Qq := R.std.1.frac_alt
  obtain ⟨g, hg, hsrc, htgt⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e he
  obtain ⟨g', hg', hsrc', htgt'⟩ := lc_main p n' 1 (m + 1) R.std.1.p_unif R.std.1.res_card R.std.1.prime.two_le
    (by have := R.std.1.two_le; omega) e' he'
  have hug : IsUnit g := (Matrix.isUnit_iff_isUnit_det _).2 hg
  have hug' : IsUnit g' := (Matrix.isUnit_iff_isUnit_det _).2 hg'
  let γ : GL (Fin (m + 1)) R.Qq := hug'.unit * hug.unit⁻¹
  have hγg : (γ : Matrix (Fin (m + 1)) (Fin (m + 1)) R.Qq) * g = g' := by
    have : γ * hug.unit = hug'.unit := by simp [γ]
    have h2 := congrArg Units.val this
    simpa using h2
  have hee : e' = mapE γ e := by
    cases e with
    | mk s tg =>
      cases e' with
      | mk s' tg' =>
        simp only at hsrc htgt hsrc' htgt'
        simp only [mapE]
        rw [hsrc, htgt, hsrc', htgt', map_colSpan, map_colSpan, ← Matrix.mul_assoc, hγg]
  obtain ⟨T, hT1, hT2⟩ := hFun p n' R m lam0 hDom γ
  have hedge : ∀ e'' : Edge R.W R.Qq (m + 1), IsEdge p n' 1 e'' → IsEdge p n' 1 (mapE γ⁻¹ e'') :=
    fun e'' h => nt_edge_map p n' 1 γ⁻¹ _ _ h
  have hsrcC : ∀ x, x ∈ CCL R lam0 t c e → T x ∈ CCL R lam0 t c (mapE γ e) := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · exact scale_alt T _ (hT1 e.src he.1) hx.1.1
    · exact scale_alt T _ (hT2 e he) hx.1.2
    · rw [Submodule.mem_iInf]
      intro e''
      rw [Submodule.mem_iInf]
      rintro ⟨h1, h2, h3⟩
      have h4 : (mapE γ⁻¹ e'').src = e.src := by
        show e''.src.map (nt_phi R.W γ⁻¹) = e.src
        rw [h2]
        exact nt_map_inv γ e.src
      have h5 : mapE γ⁻¹ e'' ≠ e := by
        intro h
        apply h3
        rw [← h, mapE_inv]
      have h6 := CCL_other R lam0 t c e (mapE γ⁻¹ e'') (hedge e'' h1) h4 h5 hx
      have h7 := apply_mem_scale_scale_of_mem_iff T _ _ (hT2 (mapE γ⁻¹ e'') (hedge e'' h1)) h6
      rwa [mapE_inv] at h7
  rw [hee]
  rcases hfac with h0 | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact Or.inl h0
  · refine Or.inr ⟨fun i => T (x i), fun l => (y l).comp T.symm.toLinearMap, fun i => hsrcC _ (hx i),
      fun l => comp_symm_mem_scale_dualLat_of_mem_iff T _ (hT2 e he) (hy l), z, M, hz, hv, fun i j => ?_⟩
    rw [← hM i j]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    unfold be
    rw [LinearMap.comp_apply, ← map_smul]
    simp

theorem nLeD {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ) (hDom : IsDominant lam0)
    (t c n : ℕ) (D : ℝ) (hD0 : 0 ≤ D) (hDc : 2 * D < c) (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e)
    (hfac : FactorsLE p (be (Kf := R.Kf) p 1 lam0) (CCL R lam0 t c e) (Re' p R.ι R.σ R.w 1 lam0 e) n D) :
    (n : ℝ) ≤ dL R lam0 :=
  nLeD_all R lam0 hDom t c n D hD0 hDc fun e' he' => nEdge R lam0 hDom t c n D e e' he he' hfac

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def LemmaSMat : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O), z1 ≠ 0 → z2 ≠ 0 →
    ∀ (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O),
    ∃ (r s : ℕ), r + s = σ ∧
      (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O),
        P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
      (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O)
        (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
        Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'')
          (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O))

def LatRetract : Prop :=
  ∀ (O K V V' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [AddCommGroup V']
    [Module K V'] [Module O V'] [IsScalarTower O K V'] (ι ι' : Type) [Fintype ι] [Fintype ι']
    (b : Module.Basis ι K V) (b' : Module.Basis ι' K V') (io : V →ₗ[K] V'),
    (∀ F, io F ∈ Submodule.span O (Set.range b') ↔ F ∈ Submodule.span O (Set.range b)) →
    ∃ ret : V' →ₗ[K] V, (∀ F, ret (io F) = F) ∧
      ∀ G ∈ Submodule.span O (Set.range b'), ret G ∈ Submodule.span O (Set.range b)

private theorem ordW_alg_lemma {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (z : O)
    (hz : z ≠ 0) :
    ordW (algebraMap O (KK O) z) = (((IsDiscreteValuationRing.addVal O z).toNat : ℤ) : WithTop ℤ) := by
  have hx : algebraMap O (KK O) z ≠ 0 := by
    simpa using (IsFractionRing.injective O (KK O)).ne hz
  have key : ∀ ab : O × nonZeroDivisors O,
      algebraMap O (KK O) z * algebraMap O (KK O) (ab.2 : O) = algebraMap O (KK O) ab.1 →
      ((IsDiscreteValuationRing.addVal O ab.1).toNat : ℤ) - (IsDiscreteValuationRing.addVal O (ab.2 : O)).toNat
        = (IsDiscreteValuationRing.addVal O z).toNat := by
    rintro ⟨a, b, hb⟩ h
    have hb0 : (b : O) ≠ 0 := nonZeroDivisors.ne_zero hb
    have h' : z * b = a := IsFractionRing.injective O (KK O) (by simpa using h)
    subst h'
    simp only
    rw [AddValuation.map_mul]
    have t1 : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
      simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hz
    have t2 : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
      simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb0
    rw [ENat.toNat_add t1 t2]
    push_cast
    ring
  unfold ordW
  rw [if_neg hx]
  exact congrArg _ (key _ (Classical.choose_spec (ordW._proof_1 (algebraMap O (KK O) z))))

theorem vLEO_one {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {D : ℝ} (hD : 0 ≤ D) :
    vLEO p (1 : O) D := by
  refine ⟨0, ?_, by simpa using hD⟩
  unfold vO vK
  rw [ordW_alg_lemma (1 : O) one_ne_zero]
  simp

theorem vLEO_mul {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {z1 z2 : O}
    (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) {D1 D2 : ℝ} (v1 : vLEO p z1 D1) (v2 : vLEO p z2 D2) :
    vLEO p (z1 * z2) (D1 + D2) := by
  obtain ⟨q1, e1, l1⟩ := v1
  obtain ⟨q2, e2, l2⟩ := v2
  rw [vO_eq h1] at e1
  rw [vO_eq h2] at e2
  have e1' := WithTop.coe_injective e1
  have e2' := WithTop.coe_injective e2
  have hv1 : IsDiscreteValuationRing.addVal O z1 ≠ ⊤ := fun h => h1 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  have hv2 : IsDiscreteValuationRing.addVal O z2 ≠ ⊤ := fun h => h2 (IsDiscreteValuationRing.addVal_eq_top_iff.1 h)
  refine ⟨q1 + q2, ?_, by push_cast; linarith⟩
  rw [vO_eq (mul_ne_zero h1 h2), IsDiscreteValuationRing.addVal_mul, ENat.toNat_add hv1 hv2, ← e1', ← e2']
  congr 1
  push_cast
  ring

theorem factorsLE_of_fintype {O Kf V V' : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] [AddCommGroup V] [Module O V] [AddCommGroup V'] [Module O V'] (p : ℕ) (be : V → V' → Kf)
    (A : Submodule O V) (A' : Submodule O V') {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → V) (y : ι → V')
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A') (z : O) (hz : z ≠ 0) {D : ℝ} (hv : vLEO p z D)
    (h : ∀ i j, be (x i) (y j) = if i = j then algebraMap O Kf z else 0) :
    FactorsLE p be A A' (Fintype.card ι) D := by
  right
  refine ⟨fun k => x ((Fintype.equivFin ι).symm k), fun k => y ((Fintype.equivFin ι).symm k),
    fun k => hx _, fun k => hy _, z, 1, hz, hv, ?_⟩
  intro i j
  simp [Matrix.one_apply, h, (Fintype.equivFin ι).symm.injective.eq_iff]

theorem scale_anti {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X]
    [Module O X] [IsScalarTower O Kf X] (w : O) {c c' : ℕ} (h : c' ≤ c) (M : Submodule O X) :
    scale (algebraMap O Kf w ^ (c : ℤ)) M ≤ scale (algebraMap O Kf w ^ (c' : ℤ)) M := by
  rintro _ ⟨m, hm, rfl⟩
  refine ⟨(w ^ (c - c')) • m, M.smul_mem _ hm, ?_⟩
  simp only [zpow_natCast, LinearMap.coe_restrictScalars, LinearMap.lsmul_apply]
  rw [← algebraMap_smul Kf (w ^ (c - c')) m, smul_smul, map_pow, ← pow_add, Nat.add_sub_cancel' h]

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem CCL_anti_c {c c' : ℕ} (h : c' ≤ c) (t : ℕ) (e : Edge R.W R.Qq (m + 1)) :
    CCL R lam0 t c e ≤ CCL R lam0 t c' e := by
  unfold CCL
  exact inf_le_inf_left _ (iInf_mono fun e' => iInf_mono fun _ => scale_anti R.w h _)

theorem wit_of_factors {A : Submodule R.O (Vsp R.Kf lam0)} {A' : Submodule R.O (Module.Dual R.Kf (Vsp R.Kf lam0))}
    {n : ℕ} {D : ℝ} (hD : 0 ≤ D) (h : FactorsLE p (be (Kf := R.Kf) p 1 lam0) A A' n D) :
    ∃ (x : Fin n → Vsp R.Kf lam0) (y : Fin n → Module.Dual R.Kf (Vsp R.Kf lam0)) (z : R.O),
      (∀ i, x i ∈ A) ∧ (∀ i, y i ∈ A') ∧ z ≠ 0 ∧ vLEO p z D ∧
      ∀ i j, be p 1 lam0 (x i) (y j) = if i = j then algebraMap R.O R.Kf z else 0 := by
  rcases h with rfl | ⟨x, y, hx, hy, z, M, hz, hv, hM⟩
  · exact ⟨Fin.elim0, Fin.elim0, 1, fun i => i.elim0, fun i => i.elim0, one_ne_zero, vLEO_one hD,
      fun i => i.elim0⟩
  · refine ⟨x, fun j => ∑ l, M l j • y l, z, hx, fun j => A'.sum_mem fun l _ => A'.smul_mem _ (hy l),
      hz, hv, ?_⟩
    intro i j
    rw [← hM i j]
    simp only [be, LinearMap.sum_apply, LinearMap.smul_apply, Algebra.smul_def, mul_comm]

theorem be_mat {α β γ δ : Type*} [Fintype β] [Fintype γ] (u : β → Vsp R.Kf lam0)
    (v : γ → Module.Dual R.Kf (Vsp R.Kf lam0)) (G : Matrix β γ R.O)
    (hG : ∀ k k', be p 1 lam0 (u k) (v k') = algebraMap R.O R.Kf (G k k')) (P : Matrix α β R.O) (Q : Matrix γ δ R.O)
    (i : α) (l : δ) :
    be p 1 lam0 (∑ k, algebraMap R.O R.Kf (P i k) • u k) (∑ k', Q k' l • v k') =
      algebraMap R.O R.Kf ((P * G * Q) i l) := by
  have hG' : ∀ k k', ((p : R.Kf) ^ Ar 1 lam0) * v k' (u k) = algebraMap R.O R.Kf (G k k') := by
    intro k k'
    rw [← hG k k']
    simp only [be, map_smul, smul_eq_mul]
  unfold be
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Matrix.mul_apply, map_mul, smul_eq_mul, Algebra.smul_def, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← hG' k k']
  ring

end Clean

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

variable {p n' : ℕ} (R : RS p n') {m : ℕ}

theorem RS.pK_ne : (p : R.Kf) ≠ 0 := by
  obtain ⟨hS, hw, -, -⟩ := R.std
  haveI := hS.frac_O
  have hO : (p : R.O) ≠ 0 := by
    rw [← hS.w_sq]
    exact pow_ne_zero _ hw.ne_zero
  intro h
  apply hO
  apply IsFractionRing.injective R.O R.Kf
  rw [map_zero, map_natCast]
  exact h

theorem be_pull (lam mu : Fin n' → Fin (m + 1) → ℤ) (f : Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf mu)
    (g : Module.Dual R.Kf (Vsp R.Kf mu)) (v : Vsp R.Kf lam) :
    be p 1 lam v (((p : R.Kf) ^ (Ar 1 mu - Ar 1 lam)) • (g ∘ₗ f)) = be p 1 mu (f v) g := by
  unfold be
  rw [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← zpow_add₀ R.pK_ne, sub_add_cancel]

theorem cloud_count (hS : LemmaSMat) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis)
    (H Hp lam : Fin n' → Fin (m + 1) → ℤ) (hdH : IsDominant H) (hdHp : IsDominant Hp)
    (e : Edge R.W R.Qq (m + 1)) (he : IsEdge p n' 1 e) (t c₂ c₃ : ℕ) (hc : c₃ ≤ c₂) (D₁ : ℝ) (hD : 0 ≤ D₁)
    (hDc : 4 * D₁ < c₂) (nb kk : ℕ) (io : Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf Hp)
    (U : Fin nb → Vsp R.Kf H →ₗ[R.Kf] Vsp R.Kf lam) (L : Fin nb → Vsp R.Kf lam →ₗ[R.Kf] Vsp R.Kf Hp)
    (ka : Fin nb → ℕ) (hka : ∀ b, ka b ≤ kk)
    (h24 : ∀ a b F, L a (U b F) = if a = b then ((p : R.Kf) ^ ka b) • io F else 0)
    (hiso : ∀ F, io F ∈ Re p R.ι R.σ R.w 1 Hp e ↔ F ∈ Re p R.ι R.σ R.w 1 H e)
    (hio : ∀ F ∈ CCL R H t c₂ e, io F ∈ CCL R Hp t c₂ e)
    (hU : ∀ b, ∀ F ∈ CCL R H t c₂ e, U b F ∈ CCL R lam t c₂ e)
    (hL : ∀ a, ∀ g ∈ CCL' R Hp t c₂ e, ((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (g ∘ₗ L a) ∈ CCL' R lam t c₃ e)
    (n1 n2 : ℕ) (f1 : FacL R H t c₂ e n1 D₁) (f2 : FacL R Hp t c₂ e n2 D₁) :
    ∃ r : ℕ, (n1 : ℝ) + n2 - dL R Hp ≤ r ∧ FacL R lam t c₃ e (nb * r) (2 * D₁ + kk) := by
  classical
  have : IsFractionRing R.O R.Kf := R.std.1.frac_O
  obtain ⟨x1, y1, z1, hx1, hy1, hz1, hv1, hG1⟩ := wit_of_factors R H hD f1
  obtain ⟨x2, y2, z2, hx2, hy2, hz2, hv2, hG2⟩ := wit_of_factors R Hp hD f2
  have hw0 := R.w_ne

  obtain ⟨bH, πH, -, -, -, -, hReH, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 H hdH e he
  obtain ⟨bP, πP, -, -, -, -, hReP, -⟩ :=
    hD3 p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he
  let cH := bH.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 H (πH i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  let cP := bP.isUnitSMul (w := fun i => algebraMap R.O R.Kf R.w ^ (-order 1 Hp (πP i)))
    (fun i => (zpow_ne_zero _ hw0).isUnit)
  have hcH : Submodule.span R.O (Set.range cH) = Re p R.ι R.σ R.w 1 H e := by
    rw [← hReH]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  have hcP : Submodule.span R.O (Set.range cP) = Re p R.ι R.σ R.w 1 Hp e := by
    rw [← hReP]
    congr 2
    funext i
    exact Module.Basis.isUnitSMul_apply _ _
  obtain ⟨ret, hret1, hret2⟩ := hRet R.O R.Kf _ _ _ _ cH cP io (by intro F; rw [hcH, hcP]; exact hiso F)
  rw [hcH, hcP] at hret2

  let tt : Fin n1 → Module.Dual R.Kf (Vsp R.Kf Hp) := fun l => ((p : R.Kf) ^ (Ar 1 H - Ar 1 Hp)) • (y1 l ∘ₗ ret)
  have htt : ∀ F l, be p 1 Hp F (tt l) = be p 1 H (ret F) (y1 l) := fun F l => be_pull R Hp H ret (y1 l) F
  have httm : ∀ l, tt l ∈ Re' p R.ι R.σ R.w 1 Hp e := fun l =>
    ((hBP p n' R.W R.Qq R.O R.Kf R.ι R.σ R.jO R.w R.std.1 m 1 Hp hdHp e he).1 (tt l)).2 fun F hF => by
      rw [htt]
      obtain ⟨b, hb⟩ := be_Re R H e (hret2 F hF) (hy1 l).1.2
      exact ⟨b, hb.symm⟩
  have hGt : ∀ k k', be p 1 Hp (io (x1 k)) (tt k') =
      algebraMap R.O R.Kf ((z1 • (1 : Matrix (Fin n1) (Fin n1) R.O)) k k') := by
    intro k k'
    rw [htt, hret1, hG1, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hNint : ∀ i b, ∃ g : R.O, be p 1 Hp (io (x1 i)) (y2 b) = algebraMap R.O R.Kf g :=
    fun i b => be_Re R Hp e (hio _ (hx1 i)).1.2 (hy2 b).1.2
  choose Nm hNm using hNint
  have hBint : ∀ a l, ∃ g : R.O, be p 1 Hp (x2 a) (tt l) = algebraMap R.O R.Kf g :=
    fun a l => be_Re R Hp e (hx2 a).1.2 (httm l)
  choose Bm hBm using hBint
  obtain ⟨r, s, hrs, ⟨P, Q, hPQ⟩, ⟨P', P'', M, hPP, hblk⟩⟩ :=
    hS R.O n1 n2 z1 z2 hz1 hz2 (Matrix.of Nm) (Matrix.of Bm)
  have hz12 : z1 * z2 ≠ 0 := mul_ne_zero hz1 hz2
  have hv12 : vLEO p (z1 * z2) (2 * D₁) := by
    have := vLEO_mul hz1 hz2 hv1 hv2
    rwa [← two_mul] at this

  let Xb : Fin s ⊕ Fin n2 → Vsp R.Kf Hp :=
    Sum.elim (fun i => ∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) x2
  let Yb : Fin s ⊕ Fin n2 → Module.Dual R.Kf (Vsp R.Kf Hp) := Sum.elim (fun l => ∑ k, P'' k l • tt k) y2
  have hXb : ∀ i, Xb i ∈ CCL R Hp t c₂ e := by
    rintro (i | a)
    · refine Submodule.sum_mem _ fun k _ => ?_
      rw [algebraMap_smul]
      exact Submodule.smul_mem _ _ (hio _ (hx1 k))
    · exact hx2 a
  have hYb : ∀ i, Yb i ∈ Re' p R.ι R.σ R.w 1 Hp e := by
    rintro (l | b)
    · exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (httm k)
    · exact (hy2 b).1.2
  have hGb : ∀ i j, be p 1 Hp (Xb i) (Yb j) = algebraMap R.O R.Kf
      (Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
        (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) i j) := by
    rintro (i | a) (l | b)
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (∑ k, P'' k l • tt k) = _
      rw [be_mat R Hp (fun k => io (x1 k)) tt _ hGt P' P'' i l, Matrix.fromBlocks_apply₁₁]
      congr 1
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPP]
    · show be p 1 Hp (∑ k, algebraMap R.O R.Kf (P' i k) • io (x1 k)) (y2 b) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [be_sum_left, Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hNm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (∑ k, P'' k l • tt k) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [be_sum, Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => by rw [hBm, map_mul, Matrix.of_apply]
    · show be p 1 Hp (x2 a) (y2 b) = _
      rw [hG2, Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> simp
  have hbadF : FactorsLE p (be (Kf := R.Kf) p 1 Hp) (CCL R Hp t c₂ e) (Re' p R.ι R.σ R.w 1 Hp e)
      (Fintype.card (Fin s ⊕ Fin n2)) (2 * D₁) := by
    refine factorsLE_of_fintype p _ _ _ Xb (fun j => ∑ l, M l j • Yb l) hXb
      (fun j => Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hYb l)) (z1 * z2) hz12 hv12 fun i j => ?_
    rw [be_sum]
    have : ∑ l, be p 1 Hp (Xb i) (Yb l) * algebraMap R.O R.Kf (M l j) = algebraMap R.O R.Kf
        ((Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) R.O)) (P' * Matrix.of Nm) (Matrix.of Bm * P'')
          (z2 • (1 : Matrix (Fin n2) (Fin n2) R.O)) * M) i j) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.mul_apply, map_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [hGb, map_mul]
    rw [this, hblk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hbad : ((s + n2 : ℕ) : ℝ) ≤ dL R Hp := by
    have hcard : Fintype.card (Fin s ⊕ Fin n2) = s + n2 := by simp
    rw [hcard] at hbadF
    exact nLeD R Hp hdHp t c₂ (s + n2) (2 * D₁) (by linarith) (by linarith) e he hbadF

  refine ⟨r, ?_, ?_⟩
  · have h1 : ((r + s : ℕ) : ℝ) = n1 := by exact_mod_cast hrs
    push_cast at h1 hbad
    linarith
  let Fg : Fin r → Vsp R.Kf H := fun i => ∑ k, algebraMap R.O R.Kf (P i k) • x1 k
  let gg : Fin r → Module.Dual R.Kf (Vsp R.Kf Hp) := fun j => ∑ b, Q b j • y2 b
  have hFg : ∀ i, Fg i ∈ CCL R H t c₂ e := fun i => by
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [algebraMap_smul]
    exact Submodule.smul_mem _ _ (hx1 k)
  have hgg : ∀ j, gg j ∈ CCL' R Hp t c₂ e := fun j =>
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (hy2 b)
  have hFgg : ∀ i j, be p 1 Hp (io (Fg i)) (gg j) = if i = j then algebraMap R.O R.Kf (z1 * z2) else 0 := by
    intro i j
    have e1 : io (Fg i) = ∑ k, algebraMap R.O R.Kf (P i k) • io (x1 k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fg, map_sum, map_smul]
    rw [e1, be_mat R Hp (fun k => io (x1 k)) y2 (Matrix.of Nm) (fun k k' => hNm k k') P Q i j, hPQ,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have hcardg : Fintype.card (Fin nb × Fin r) = nb * r := by simp
  rw [← hcardg]
  refine factorsLE_of_fintype p _ _ _ (fun x : Fin nb × Fin r => U x.1 (Fg x.2))
    (fun y : Fin nb × Fin r => ((p : R.O) ^ (kk - ka y.1)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg y.2 ∘ₗ L y.1)))
    (fun x => CCL_anti_c R lam hc t e (hU x.1 _ (hFg x.2)))
    (fun y => Submodule.smul_mem _ _ (hL y.1 _ (hgg y.2)))
    ((p : R.O) ^ kk * (z1 * z2)) (mul_ne_zero (pow_ne_zero _ R.p_ne) hz12)
    (vLEO_pow_mul R.p_ne R.p_not_unit hz12 kk hv12) ?_
  rintro ⟨b, i⟩ ⟨a, j⟩
  show be p 1 lam (U b (Fg i)) (((p : R.O) ^ (kk - ka a)) •
      (((p : R.Kf) ^ (Ar 1 Hp - Ar 1 lam)) • (gg j ∘ₗ L a))) = _
  rw [be_smul, be_pull, h24]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, be_smulK_left, hFgg]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      simp only [map_mul, map_pow, map_natCast]
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (hka a)]
    · have : ((a, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hij (Prod.mk.inj h).2
      rw [if_neg hij, if_neg this, mul_zero, mul_zero]
  · have : ((b, i) : Fin nb × Fin r) ≠ (a, j) := fun h => hab (Prod.mk.inj h).1.symm
    rw [if_neg hab, if_neg this]
    simp [be]

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames

def RestCloudMaps : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (mm : ℕ), 1 ≤ mm → ∀ (TT : Finset (Fin n')) (a ccl : ℕ) (aw bw : Fin n' → ℤ)
    (lam0 : Fin n' → Fin (mm + 1 + 1) → ℤ) (A B : TT → ℕ),
    IsBaseWeight TT aw bw ccl lam0 → IsDominant lam0 → (∀ s, s ∉ TT → lam0 s = 0) →
    (∀ s : TT, (A s : ℤ) = aw s - ccl ∧ (B s : ℤ) = bw s - ccl) → 2 * ccl ≤ 8 * a →
    ∀ e : Edge R.W R.Qq (mm + 1 + 1), IsEdge p n' 1 e →
    ∃ (nb : ℕ) (io : Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (U : Fin nb → Vsp R.Kf (flatW (mm + 1) A B) →ₗ[R.Kf] Vsp R.Kf lam0)
      (L : Fin nb → Vsp R.Kf lam0 →ₗ[R.Kf]
        Vsp R.Kf (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)))
      (ka : Fin nb → ℕ),
      (nb : ℝ) = dimCl TT lam0 ∧ (∀ b, ka b ≤ TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) ∧
      (∀ a' b F, L a' (U b F) = if a' = b then ((p : R.Kf) ^ ka b) • io F else 0) ∧
      (∀ F, io F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) e ↔
        F ∈ Re p R.ι R.σ R.w 1 (flatW (mm + 1) A B) e) ∧
      ∀ t c₂ : ℕ, 2 * TT.card * ccl ≤ c₂ →
        (∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e,
          io F ∈ CCL R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e) ∧
        (∀ b, ∀ F ∈ CCL R (flatW (mm + 1) A B) t c₂ e, U b F ∈ CCL R lam0 t c₂ e) ∧
        (∀ a', ∀ g ∈ CCL' R (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) t c₂ e,
          ((p : R.Kf) ^ (Ar 1 (flatW (mm + 1) (fun s => A s + 2 * ccl) (fun s => B s + 2 * ccl)) - Ar 1 lam0)) •
            (g ∘ₗ L a') ∈ CCL' R lam0 t (c₂ - 2 * TT.card * ccl) e)

theorem lemmaSMat : LemmaSMat := fun O _ _ _ σ ρ z1 z2 h1 h2 N B => KP.lemmaSMat σ ρ z1 z2 h1 h2 N B

theorem cloud_prop_of_maps_retraction_basis (hC : RestCloudMaps) (hRet : LatRetract) (hBP : BePerfect) (hD3 : DualHeightBasis) : CloudLowerBoundWeyl := by
  intro p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 t c₂ D₁ κ₁ κ₂ hD hDc hNc hκ0 hκ1 hκ2 hρ1 hρ2 e he
  obtain ⟨nb, io, U, L, ka, hnb, hka, h24, hiso, hmem⟩ :=
    hC p n' R mm hmm TT a ccl aw bw lam0 A B hBase hDom hzero hAB h8 e he
  obtain ⟨hio, hU, hL⟩ := hmem t c₂ hNc
  obtain ⟨n1, hX1, f1⟩ := hρ1 e he
  obtain ⟨n2, hX2, f2⟩ := hρ2 e he
  obtain ⟨r, hr, hfac⟩ := cloud_count R lemmaSMat hRet hBP hD3 _ _ lam0 (flattened_weight_dominant _ _ _) (flattened_weight_dominant _ _ _) e he t c₂
    (c₂ - 2 * TT.card * ccl) (Nat.sub_le _ _) D₁ hD hDc nb (TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊) io U L ka hka h24 hiso hio
    hU hL n1 n2 f1 f2
  refine ⟨nb * r, ?_, ?_⟩
  · rw [← hnb]
    push_cast
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    linarith
  · have : (2 * D₁ + ((TT.card * ⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) : ℝ)) =
        2 * D₁ + (TT.card : ℝ) * (⌈kappaOneExponent p a (mm + 1)⌉₊ : ℕ) := by push_cast; ring
    rw [← this]
    exact hfac

end Formalism.MainNotions.flipOneThree.Pf

end
