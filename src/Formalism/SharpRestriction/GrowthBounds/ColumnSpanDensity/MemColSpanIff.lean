module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoLowerBoundOfEdgeCount
public import Formalism.SharpRestriction.GrowthBounds.LatticeSystems

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RhoUpperBoundOfEdgeCount
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def RestEdgeCountSrc : Prop :=
  ∀ (p n' : ℕ) (R : RS p n') (k : ℕ), 1 ≤ k → ∀ L : Submodule R.W (Fin k → R.Qq), IsLattice R.W L →
    ∃ (Ne : ℕ) (es : Fin Ne → Edge R.W R.Qq k), Function.Injective es ∧
      (∀ i, IsEdge p n' 1 (es i) ∧ (es i).src = L) ∧ gaussianNumber (p ^ n') k ≤ Ne

theorem dvd_w_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O}
    (hw : Irreducible w) (hsq : w ^ 2 = (p : O)) {z : O} (hz : z ≠ 0) {D : ℝ} {c : ℕ} (hc : 2 * D < c)
    (h : vLEO p z D) : z ∣ w ^ (c - 1) := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have hram : ramE p O = 2 := by
    unfold ramE
    rw [← hsq, AddValuation.map_pow, IsDiscreteValuationRing.addVal_uniformizer hw]
    simp
  rw [hram] at hq
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) < (c : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    linarith
  have hlt : (IsDiscreteValuationRing.addVal O z).toNat < c := by exact_mod_cast hreal
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ c - 1 := by omega
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer hw, ← ENat.coe_toNat hzt, nsmul_eq_mul, mul_one]
  exact_mod_cast hnat

theorem isUnit_det_of_one_add' {O ι : Type*} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι O) (h : ∀ i l, P i l - (1 : Matrix ι ι O) i l ∈ IsLocalRing.maximalIdeal O) :
    IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix ι ι O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

section Clean

variable {p n' : ℕ} (R : RS p n') {m : ℕ} (lam0 : Fin n' → Fin (m + 1) → ℤ)

theorem be_smulK_left (c : R.Kf) (F : Vsp R.Kf lam0) (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (c • F) G = c * be p 1 lam0 F G := by
  unfold be
  rw [smul_comm, map_smul, smul_eq_mul]

theorem be_sum_left {ι : Type*} (s : Finset ι) (c : ι → R.Kf) (F : ι → Vsp R.Kf lam0)
    (G : Module.Dual R.Kf (Vsp R.Kf lam0)) :
    be p 1 lam0 (∑ i ∈ s, c i • F i) G = ∑ i ∈ s, c i * be p 1 lam0 (F i) G := by
  unfold be
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm, map_smul, smul_eq_mul]

theorem be_scale_Re (e : Edge R.W R.Qq (m + 1)) (c : ℕ) {F : Vsp R.Kf lam0}
    {G : Module.Dual R.Kf (Vsp R.Kf lam0)}
    (hF : F ∈ scale (algebraMap R.O R.Kf R.w ^ (c : ℤ)) (Re p R.ι R.σ R.w 1 lam0 e))
    (hG : G ∈ Re' p R.ι R.σ R.w 1 lam0 e) :
    ∃ b : R.O, be p 1 lam0 F G = algebraMap R.O R.Kf (R.w ^ c * b) := by
  unfold scale at hF
  obtain ⟨F0, hF0, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨b, hb⟩ := be_Re R lam0 e hF0 hG
  refine ⟨b, ?_⟩
  simp only [LinearMap.restrictScalars_apply, LinearMap.lsmul_apply, zpow_natCast]
  rw [be_smulK_left, hb, ← map_pow, ← map_mul]

end Clean

theorem rho_upper_bound_of_edge_count (hcnt : RestEdgeCountSrc) : RhoUpperBoundSmallDepth := by
  classical
  intro p n' R m lam0 hDom t c n D hD0 hDc hfac
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
      (∀ a, x a ∈ CCL R lam0 t c (es i)) ∧ (∀ a, y a ∈ CCL' R lam0 t c (es i)) ∧
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
      obtain ⟨b', hb⟩ := be_scale_Re R lam0 (es l) c hXs (hy l b).1.2
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

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.LatticeSystems

section Gen

variable {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] {k : ℕ}

def emb (w : Fin k → W) : Fin k → Qq := fun i => algebraMap W Qq (w i)

abbrev mapM (N : Matrix (Fin k) (Fin k) W) : Matrix (Fin k) (Fin k) Qq := (algebraMap W Qq).mapMatrix N

theorem mem_colSpan_iff (h : Matrix (Fin k) (Fin k) Qq) (x : Fin k → Qq) :
    x ∈ colSpan W h ↔ ∃ y : Fin k → W, x = fun i => ∑ c, h i c * algebraMap W Qq (y c) := by
  unfold colSpan
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [Finset.sum_apply, Algebra.smul_def, mul_comm]

theorem colSpan_mul_le (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) :
    colSpan W (h * mapM N) ≤ colSpan W h := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, rfl⟩
  refine (mem_colSpan_iff h _).2 ⟨fun j => N j c, funext fun i => ?_⟩
  simp [Matrix.mul_apply, mapM, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem colSpan_unimod (h : Matrix (Fin k) (Fin k) Qq) (N : Matrix (Fin k) (Fin k) W) (hN : IsUnit N.det) :
    colSpan W (h * mapM N) = colSpan W h := by
  refine le_antisymm (colSpan_mul_le h N) ?_
  have h1 : h * mapM N * mapM N⁻¹ = h := by
    rw [Matrix.mul_assoc, ← map_mul, Matrix.mul_nonsing_inv N hN, map_one, Matrix.mul_one]
  calc colSpan W h = colSpan W (h * mapM N * mapM N⁻¹) := by rw [h1]
    _ ≤ colSpan W (h * mapM N) := colSpan_mul_le _ _

theorem map_colSpan (g : GL (Fin k) Qq) (h : Matrix (Fin k) (Fin k) Qq) :
    (colSpan W h).map (nt_phi W g) = colSpan W ((g : Matrix (Fin k) (Fin k) Qq) * h) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2

def dj (j : Fin k) (c : Qq) : Matrix (Fin k) (Fin k) Qq := Matrix.diagonal fun i => if i = j then c else 1

theorem dj_det (j : Fin k) (c : Qq) : (dj j c).det = c := by
  simp [dj, Matrix.det_diagonal]

theorem dj_mul (j : Fin k) (c d : Qq) : dj j c * dj j d = dj j (c * d) := by
  simp only [dj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

theorem dj_one (j : Fin k) : dj j (1 : Qq) = 1 := by
  simp [dj]

end Gen

section Base

variable {p n' : ℕ} (R : RS p n') {k : ℕ}

theorem RS.injW : Function.Injective (algebraMap R.W R.Qq) := by
  haveI := R.std.1.frac_alt
  exact IsFractionRing.injective R.W R.Qq

theorem RS.pQ_ne : (p : R.Qq) ≠ 0 := by
  have h1 : (p : R.W) ≠ 0 := R.std.1.p_unif.ne_zero
  rw [← map_natCast (algebraMap R.W R.Qq)]
  exact fun h => h1 ((map_eq_zero_iff _ (RS.injW R)).1 h)

def embLin (R : RS p n') (k : ℕ) : (Fin k → R.W) →ₗ[R.W] (Fin k → R.Qq) where
  toFun := emb
  map_add' := by intro x y; funext i; simp [emb]
  map_smul' := by intro c x; funext i; simp [emb, Algebra.smul_def]

theorem embLin_inj : Function.Injective (embLin R k) := by
  intro x y hxy
  funext i
  exact RS.injW R (congrFun hxy i)

theorem colSpan_one_eq : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) = LinearMap.range (embLin R k) := by
  ext x
  rw [mem_colSpan_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]
  · rintro ⟨y, rfl⟩
    refine ⟨y, funext fun i => ?_⟩
    simp [embLin, emb, Matrix.one_apply]

theorem mem_dj_iff (j : Fin k) (x : Fin k → R.Qq) :
    x ∈ colSpan R.W (dj j (p : R.Qq)) ↔ ∃ y : Fin k → R.W, x = emb (fun i => (if i = j then (p : R.W) else 1) * y i) := by
  rw [mem_colSpan_iff]
  constructor <;> rintro ⟨y, rfl⟩ <;> refine ⟨y, funext fun i => ?_⟩ <;>
    by_cases hij : i = j <;> simp [dj, emb, Matrix.diagonal_apply, hij]

theorem baseEdge (j : Fin k) :
    IsEdge p n' 1 (⟨colSpan R.W (dj j (p : R.Qq)), colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)⟩ :
      Edge R.W R.Qq k) := by
  classical
  have hstd := R.std.1
  have htgt : ∀ x, x ∈ colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ↔ ∃ y, embLin R k y = x := by
    intro x
    rw [colSpan_one_eq R]
    exact LinearMap.mem_range
  have hsrc : ∀ x, x ∈ colSpan R.W (dj j (p : R.Qq)) ↔
      ∃ y : Fin k → R.W, x = emb y ∧ y j ∈ Ideal.span {(p : R.W)} := by
    intro x
    rw [mem_dj_iff R]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨_, rfl, ?_⟩
      simp only [if_pos rfl]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · rintro ⟨y, rfl, hy⟩
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨fun i => if i = j then z else y i, ?_⟩
      congr 1
      funext i
      by_cases hij : i = j
      · subst hij
        simp [← hz, mul_comm]
      · simp [hij]
  let e := LinearEquiv.ofInjective (embLin R k) (embLin_inj R)
  let E : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) ≃ₗ[R.W] (Fin k → R.W) :=
    (LinearEquiv.ofEq _ _ (colSpan_one_eq R)).trans e.symm
  have hE : ∀ x, emb (E x) = (x : Fin k → R.Qq) := by
    intro x
    have h2 := congrArg Subtype.val (e.apply_symm_apply (LinearEquiv.ofEq _ _ (colSpan_one_eq R) x))
    rw [LinearEquiv.ofInjective_apply] at h2
    exact h2
  let ψ : colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq) →ₗ[R.W] R.W ⧸ Ideal.span {(p : R.W)} :=
    (Ideal.span {(p : R.W)}).mkQ ∘ₗ LinearMap.proj j ∘ₗ E.toLinearMap
  have hψ : ∀ x, ψ x = (Submodule.Quotient.mk (E x j) : R.W ⧸ Ideal.span {(p : R.W)}) := fun x => rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨E.symm (Pi.single j a), ?_⟩
    rw [hψ, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
  have hker : Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
      (colSpan R.W (dj j (p : R.Qq))) = LinearMap.ker ψ := by
    ext x
    rw [Submodule.mem_comap, LinearMap.mem_ker, hψ, Submodule.Quotient.mk_eq_zero, Submodule.subtype_apply, hsrc]
    constructor
    · rintro ⟨y, hy, hyj⟩
      have hxy : E x = y := embLin_inj R ((hE x).trans hy)
      rw [hxy]
      exact hyj
    · intro h
      exact ⟨E x, (hE x).symm, h⟩
  refine ⟨⟨dj j (p : R.Qq), ?_, rfl⟩, ⟨1, by simp, rfl⟩, ?_, ?_, ?_⟩
  · rw [dj_det]
    exact isUnit_iff_ne_zero.2 (RS.pQ_ne R)
  · intro x hx
    obtain ⟨y, rfl, -⟩ := (hsrc x).1 hx
    exact (htgt _).2 ⟨y, rfl⟩
  · intro x hx
    obtain ⟨y, rfl⟩ := (htgt x).1 hx
    refine (hsrc _).2 ⟨(p : R.W) • y, ?_, ?_⟩
    · funext i
      simp [embLin, emb, Algebra.smul_def]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · show Nat.card (↥(colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)) ⧸
      Submodule.comap (colSpan R.W (1 : Matrix (Fin k) (Fin k) R.Qq)).subtype
        (colSpan R.W (dj j (p : R.Qq)))) = p ^ (n' * 1)
    rw [hker, Nat.card_congr (ψ.quotKerEquivOfSurjective hsurj).toEquiv, hstd.res_card, mul_one]

end Base

end Formalism.MainNotions.flipOneThree.Pf

end
