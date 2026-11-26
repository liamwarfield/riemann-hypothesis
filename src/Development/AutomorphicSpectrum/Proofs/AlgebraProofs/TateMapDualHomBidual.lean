module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFlatIntegrand
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivationDivisibleOfCocomm
public import ReciprocityTheory.DualLattices.LinPairStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvdMulOfGroupLikeVal
noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDiv
open GlobalTheory.GroupLikeDerivation (extProd extProd_tmul inlHom inrHom mulHom extendHom inlHom_mul_inrHom
  exists_isGroupLikeElem)

namespace GlobalTheory.CompanionTheory.Ar.HT.CokerSharp

section Norm

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
  {O : Type} [CommRing O] [Algebra O C] {M : Type} [AddCommGroup M] [Module O M]

theorem norm_smul_le (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) (o : O) (x : C) : ‖o • x‖ ≤ ‖x‖ := by
  rw [Algebra.smul_def, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (h1 o)

theorem norm_le_of_mem_span (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) (f : M →ₗ[O] C) {s : Set M}
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ m ∈ s, ‖f m‖ ≤ r) {m : M} (hm : m ∈ Submodule.span O s) :
    ‖f m‖ ≤ r := by
  induction hm using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simpa using hr
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  | smul o x _ hx => rw [map_smul]; exact (norm_smul_le h1 _ _).trans hx

theorem bddAbove_norm (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M] (f : M →ₗ[O] C) :
    BddAbove (Set.range fun m => ‖f m‖) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := M)
  refine ⟨∑ m ∈ s, ‖f m‖, ?_⟩
  rintro _ ⟨m, rfl⟩
  refine norm_le_of_mem_span h1 f (s := s) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (fun m hm => Finset.single_le_sum (f := fun m => ‖f m‖) (fun _ _ => norm_nonneg _) hm) ?_
  rw [hs]; trivial

def supN (f : WithConv (M →ₗ[O] C)) : ℝ := ⨆ m, ‖f.ofConv m‖

theorem le_supN (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M]
    (f : WithConv (M →ₗ[O] C)) (m : M) : ‖f.ofConv m‖ ≤ supN f :=
  le_ciSup (bddAbove_norm h1 f.ofConv) m

theorem supN_le {f : WithConv (M →ₗ[O] C)} {r : ℝ} (h : ∀ m, ‖f.ofConv m‖ ≤ r) :
    supN f ≤ r := ciSup_le h

theorem supN_nonneg (f : WithConv (M →ₗ[O] C)) : 0 ≤ supN f :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem supN_smul (c : C) (f : WithConv (M →ₗ[O] C)) : supN (c • f) = ‖c‖ * supN f := by
  rw [supN, supN, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  congr 1
  ext m
  rw [← norm_mul]
  rfl

theorem supN_add_le (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M]
    (f g : WithConv (M →ₗ[O] C)) : supN (f + g) ≤ max (supN f) (supN g) :=
  supN_le fun m => (IsUltrametricDist.norm_add_le_max (f.ofConv m) (g.ofConv m)).trans
    (max_le_max (le_supN h1 f m) (le_supN h1 g m))

theorem supN_mul_le (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M] [Coalgebra O M]
    (f g : WithConv (M →ₗ[O] C)) : supN (f * g) ≤ supN f * supN g := by
  refine supN_le fun m => ?_
  have h := (Coalgebra.Repr.arbitrary O m).convMul_apply f g
  rw [h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun i _ => ?_
  rw [norm_mul]
  exact mul_le_mul (le_supN h1 f _) (le_supN h1 g _) (norm_nonneg _) (supN_nonneg _)

theorem supN_le_of_tmul {f : WithConv (M ⊗[O] M →ₗ[O] C)} {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ a b, ‖f.ofConv (a ⊗ₜ b)‖ ≤ r) : supN f ≤ r := by
  refine supN_le fun t => ?_
  induction t with
  | tmul a b => exact h a b
  | add x y hx hy =>
    rw [map_add (f := _)]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

theorem supN_eq_mul (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M]
    [Module.Finite O (M ⊗[O] M)] (f g : WithConv (M →ₗ[O] C))
    (h : WithConv (M ⊗[O] M →ₗ[O] C))
    (hh : ∀ a b, h.ofConv (a ⊗ₜ b) = f.ofConv a * g.ofConv b) :
    supN h = supN f * supN g := by
  apply le_antisymm
  · refine supN_le_of_tmul (mul_nonneg (supN_nonneg _) (supN_nonneg _)) fun a b => ?_
    rw [hh, norm_mul]
    exact mul_le_mul (le_supN h1 f _) (le_supN h1 g _) (norm_nonneg _) (supN_nonneg _)
  · rw [supN.eq_1 f, Real.iSup_mul_of_nonneg (supN_nonneg g)]
    refine ciSup_le fun a => ?_
    rw [supN.eq_1 g, Real.mul_iSup_of_nonneg (norm_nonneg _)]
    refine ciSup_le fun b => ?_
    rw [← norm_mul, ← hh]
    exact le_supN h1 h _

theorem exists_supN_pow_le (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1) [Module.Finite O M]
    [Coalgebra O M] [IsCocomm O M] {y : WithConv (M →ₗ[O] C)} (hy : IsIntegral O y) :
    ∃ K : ℝ, ∀ k : ℕ, supN (y ^ k) ≤ K := by
  obtain ⟨s, hs⟩ := hy.fg_adjoin_singleton
  refine ⟨∑ f ∈ s, supN f, fun k => supN_le fun m => ?_⟩
  have hk : y ^ k ∈ Submodule.span O (s : Set (WithConv (M →ₗ[O] C))) := by
    rw [hs]
    exact pow_mem (Algebra.self_mem_adjoin_singleton _ y) k
  let ev : WithConv (M →ₗ[O] C) →ₗ[O] C :=
    { toFun := fun f => f.ofConv m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact norm_le_of_mem_span h1 ev (Finset.sum_nonneg fun _ _ => supN_nonneg _)
    (fun f hf => (le_supN h1 f m).trans
      (Finset.single_le_sum (f := fun f => supN f) (fun _ _ => supN_nonneg _) hf)) hk

end Norm

section Main

theorem dvd_iff_norm {C : Type} [NontriviallyNormedField C] {O : Type} [CommRing O] [Algebra O C]
    (hinj : Function.Injective (algebraMap O C)) (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1)
    (h2 : ∀ z : C, ‖z‖ ≤ 1 → z ∈ (algebraMap O C).range) {q : O} (hq : q ≠ 0) (x : O) :
    q ∣ x ↔ ‖(algebraMap O C q)⁻¹ * algebraMap O C x‖ ≤ 1 := by
  have hq' : algebraMap O C q ≠ 0 := fun h => hq (hinj (by rw [h, map_zero]))
  constructor
  · rintro ⟨z, rfl⟩
    rw [map_mul, inv_mul_cancel_left₀ hq']
    exact h1 z
  · intro h
    obtain ⟨z, hz⟩ := h2 _ h
    refine ⟨z, hinj ?_⟩
    rw [map_mul, hz, mul_inv_cancel_left₀ hq']

theorem dvd_mul_of_groupLike (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] (p : ℕ) [Fact p.Prime] (hp : ‖(p : C)‖ = (p : ℝ)⁻¹)
    (O : Type) [CommRing O] [Algebra O C] (hinj : Function.Injective (algebraMap O C))
    (h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1)
    (h2 : ∀ z : C, ‖z‖ ≤ 1 → z ∈ (algebraMap O C).range)
    (hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range)
    (A : Type) [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A]
    [Module.Finite O A] [Module.Projective O A] (q : O) (hq : q ≠ 0)
    (D : A →ₗ[O] O)
    (hD : ∀ a b : A, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : A, IsGroupLikeElem O u → q ∣ D u)
    (c : O) (hc : ‖algebraMap O C c‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1)))) (a : A) :
    q ∣ c * D a := by
  set y : WithConv (A →ₗ[O] C) := (algebraMap O C q)⁻¹ • extendHom O C A (toConv D) with hy
  have hya : ∀ a, y.ofConv a = (algebraMap O C q)⁻¹ * algebraMap O C (D a) := fun _ => rfl
  have : IsScalarTower O C (WithConv (A →ₗ[O] C)) := ⟨fun o c f => WithConv.ext (LinearMap.ext fun a => by
    change (o • c) * f.ofConv a = o • (c * f.ofConv a)
    rw [smul_mul_assoc])⟩
  have hint : IsIntegral O y :=
    GlobalTheory.IntegralOfPointValues.isIntegral_inv_smul_of_closed (B₀ := CartierDual O A) hinj hcl
      (extendHom O C A) (toConv D) q hq fun χ => by
        obtain ⟨u, h3, h4⟩ := exists_isGroupLikeElem χ
        rw [← h4]
        exact hu u h3
  have key := GlobalTheory.NearlyPrimitive.norm_smul_le_one C p hp _ _ supN supN (mulHom O C A)
    (inlHom O C A) (inrHom O C A) supN_smul supN_smul supN_nonneg
    supN_nonneg (supN_add_le h1) (supN_mul_le h1)
    (fun f => supN_le fun t => le_supN h1 f _)
    (fun f g => supN_eq_mul h1 f g _ fun a b => by rw [inlHom_mul_inrHom, extProd_tmul])
    y (exists_supN_pow_le h1 hint)
    (supN_le_of_tmul zero_le_one fun a b => by
      have h := (dvd_iff_norm hinj h1 h2 hq _).1 (hD a b)
      convert h using 2
      change y.ofConv (a * b) - (extProd y 1).ofConv (a ⊗ₜ b) - (extProd 1 y).ofConv (a ⊗ₜ b) = _
      rw [extProd_tmul, extProd_tmul, hya, hya, hya, LinearMap.convOne_apply,
        LinearMap.convOne_apply]
      simp only [map_sub, map_mul]
      change _ - _ * algebraMap O C (counit (R := O) b) -
        algebraMap O C (counit (R := O) a) * _ = _
      ring)
    (algebraMap O C c) hc
  rw [dvd_iff_norm hinj h1 h2 hq]
  have h : (algebraMap O C q)⁻¹ * algebraMap O C (c * D a) = (algebraMap O C c • y).ofConv a := by
    change _ = algebraMap O C c * y.ofConv a
    rw [hya, map_mul]
    ring
  rw [h]
  exact (le_supN h1 _ a).trans key

end Main

section Diag

theorem exists_diag {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
    [Algebra O C] (hv : v.Integers O) {F : Type} [AddCommGroup F] [Module O F] {r m : ℕ}
    (b : Module.Basis (Fin r) O F) (g : Fin m → F) :
    ∃ (φ : Fin r → F →ₗ[O] O) (e : Fin r → F) (d : Fin r → O),
      (∀ j, φ j (e j) = 1) ∧ (∀ w, w = ∑ j, φ j w • e j) ∧ (∀ j k, d j ∣ φ j (g k)) ∧
      ∀ j, d j • e j ∈ Submodule.span O (Set.range g) := by
  classical
  let A : Matrix (Fin r) (Fin m) O := fun j k => b.equivFun (g k) j
  obtain ⟨P, Q, a, hP, hQ, hD⟩ := ReciprocityTheory.PGsh.Up.Smith.smith_mat (v := v) hv r m A
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hQQ : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQ
  let φ : Fin r → F →ₗ[O] O := fun j =>
    LinearMap.proj j ∘ₗ P.mulVecLin ∘ₗ b.equivFun.toLinearMap
  let e : Fin r → F := fun j => b.equivFun.symm fun i => P⁻¹ i j
  have hφ : ∀ j w, φ j w = ∑ i, P j i * b.equivFun w i := fun j w => rfl
  have he : ∀ j i, b.equivFun (e j) i = P⁻¹ i j := fun j i => by
    change b.equivFun (b.equivFun.symm _) i = _
    rw [b.equivFun.apply_symm_apply]
  have hφe : ∀ l j, φ l (e j) = (1 : Matrix (Fin r) (Fin r) O) l j := fun l j => by
    rw [hφ, ← hPP, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [he]
  have hsum : ∀ w, w = ∑ j, φ j w • e j := fun w => by
    apply b.equivFun.injective
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_apply]
    have h := congrFun (Matrix.mulVec_mulVec (b.equivFun w) P⁻¹ P) i
    rw [hPP', Matrix.one_mulVec] at h
    rw [← h]
    change ∑ j, P⁻¹ i j * (P.mulVec (b.equivFun w)) j = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, Pi.smul_apply, he, smul_eq_mul, mul_comm]
    rfl
  have hφg : ∀ j k, φ j (g k) = (P * A) j k := fun j k => by
    rw [hφ, Matrix.mul_apply]
  have hPA : ∀ j k, (P * A) j k =
      ∑ l : Fin m, (if (l : ℕ) = (j : ℕ) then a j else 0) * Q⁻¹ l k := fun j k => by
    have h : P * A = P * A * Q * Q⁻¹ := by rw [Matrix.mul_assoc (P * A), hQQ, Matrix.mul_one]
    rw [h, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => by rw [hD]
  refine ⟨φ, e, fun j => if (j : ℕ) < m then a j else 0, fun j => ?_, hsum, fun j k => ?_,
    fun j => ?_⟩
  · rw [hφe, Matrix.one_apply_eq]
  · rw [hφg, hPA]
    change (if (j : ℕ) < m then a j else 0) ∣ _
    by_cases h : (j : ℕ) < m
    · rw [if_pos h]
      refine Finset.dvd_sum fun l _ => ?_
      split_ifs
      · exact dvd_mul_right _ _
      · simp
    · have h0 : ∑ l : Fin m, (if (l : ℕ) = (j : ℕ) then a j else 0) * Q⁻¹ l k = 0 :=
        Finset.sum_eq_zero fun l _ => by rw [if_neg (fun hl : (l : ℕ) = j => h (hl ▸ l.2)), zero_mul]
      rw [h0]
      exact dvd_zero _
  · by_cases h : (j : ℕ) < m
    · simp only [if_pos h]
      let x : F := ∑ k, Q k ⟨j, h⟩ • g k
      have hx : x ∈ Submodule.span O (Set.range g) :=
        Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      have hφx : ∀ i, φ i x = if (j : ℕ) = (i : ℕ) then a i else 0 := fun i => by
        have h1 : φ i x = (P * A * Q) i ⟨j, h⟩ := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Matrix.mul_apply, map_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul, hφg, smul_eq_mul, mul_comm]
        rw [h1, hD]
      have hxe : a j • e j = x := by
        rw [hsum x, Finset.sum_eq_single j]
        · rw [hφx, if_pos rfl]
        · intro i _ hij
          rw [hφx, if_neg fun hh => hij (Fin.ext hh.symm), zero_smul]
        · simp
      rwa [hxe]
    · simp only [if_neg h, zero_smul]
      exact zero_mem _

end Diag

section Renorm

variable {C : Type} [Field C] (v : Valuation C NNReal)

theorem rpow_add_le (s : ℝ) (hs : 0 < s) (x y : C) :
    ((v (x + y) : NNReal) : ℝ) ^ s ≤ max (((v x : NNReal) : ℝ) ^ s) (((v y : NNReal) : ℝ) ^ s) := by
  rcases le_max_iff.1 (v.map_add x y) with h | h
  · exact le_max_of_le_left (Real.rpow_le_rpow (NNReal.coe_nonneg _) (by exact_mod_cast h) hs.le)
  · exact le_max_of_le_right (Real.rpow_le_rpow (NNReal.coe_nonneg _) (by exact_mod_cast h) hs.le)

def absOf (s : ℝ) (hs : 0 < s) : AbsoluteValue C ℝ where
  toFun x := ((v x : NNReal) : ℝ) ^ s
  map_mul' x y := by
    rw [map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
  nonneg' x := Real.rpow_nonneg (NNReal.coe_nonneg _) _
  eq_zero' x := by
    rw [Real.rpow_eq_zero (NNReal.coe_nonneg _) hs.ne', NNReal.coe_eq_zero, map_eq_zero]
  add_le' x y := (rpow_add_le v s hs x y).trans (max_le_add_of_nonneg
    (Real.rpow_nonneg (NNReal.coe_nonneg _) _) (Real.rpow_nonneg (NNReal.coe_nonneg _) _))

theorem dvd_mul_of_groupLike_val (p : ℕ) [Fact p.Prime] [hac : IsAlgClosed C] [h0 : CharZero C]
    (O : Type) [CommRing O] [hA : Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1)
    (B : Type) [CommRing B] [Bialgebra O B] [Coalgebra.IsCocomm O B]
    [Module.Finite O B] [Module.Projective O B] (q : O) (hq : q ≠ 0)
    (D : B →ₗ[O] O)
    (hD : ∀ a b : B, q ∣ D (a * b) - Coalgebra.counit (R := O) a * D b -
      Coalgebra.counit (R := O) b * D a)
    (hu : ∀ u : B, IsGroupLikeElem O u → q ∣ D u)
    (κ : O) (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (a : B) :
    q ∣ κ * D a := by
  have hpp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
  have hpc : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hpp.ne_zero
  have hv0 : 0 < ((v (p : C) : NNReal) : ℝ) := by
    have : v (p : C) ≠ 0 := (Valuation.ne_zero_iff v).2 hpc
    exact_mod_cast pos_iff_ne_zero.2 this
  have hv1 : ((v (p : C) : NNReal) : ℝ) < 1 := by exact_mod_cast hp
  have hL : Real.log (v (p : C) : NNReal) < 0 := Real.log_neg hv0 hv1
  obtain ⟨s, hs, hps⟩ : ∃ s : ℝ, 0 < s ∧ ((v (p : C) : NNReal) : ℝ) ^ s = (p : ℝ)⁻¹ := by
    refine ⟨Real.log p / (-Real.log (v (p : C) : NNReal)),
      div_pos (Real.log_pos hp1) (neg_pos.2 hL), ?_⟩
    rw [Real.rpow_def_of_pos hv0, show Real.log (v (p : C) : NNReal) *
      (Real.log p / (-Real.log (v (p : C) : NNReal))) = -Real.log p by
        field_simp [hL.ne], Real.exp_neg, Real.exp_log (by linarith)]
  letI nf : NormedField C := (absOf v s hs).toNormedField
  have hnorm : ∀ x : C, ‖x‖ = ((v x : NNReal) : ℝ) ^ s := fun x => rfl
  have hpn : ‖(p : C)‖ = (p : ℝ)⁻¹ := by rw [hnorm, hps]
  letI nnf : NontriviallyNormedField C := NontriviallyNormedField.ofNormNeOne
    ⟨(p : C), hpc, by rw [hpn]; exact (inv_lt_one_of_one_lt₀ hp1).ne⟩
  have ult : IsUltrametricDist C :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      fun x y => rpow_add_le v s hs x y
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have h1 : ∀ o : O, ‖algebraMap O C o‖ ≤ 1 := fun o => by
    rw [hnorm]
    exact Real.rpow_le_one (NNReal.coe_nonneg _) (by exact_mod_cast hv.map_le_one o) hs.le
  have h2 : ∀ z : C, ‖z‖ ≤ 1 → z ∈ (algebraMap O C).range := fun z hz => by
    refine hv.exists_of_le_one ?_
    by_contra hlt
    have h3 : (1 : ℝ) < ((v z : NNReal) : ℝ) := by exact_mod_cast not_le.1 hlt
    rw [hnorm] at hz
    exact absurd (Real.one_lt_rpow h3 hs) (not_lt.2 hz)
  have hcl : ∀ z : C, IsIntegral O z → z ∈ (algebraMap O C).range := fun z hz =>
    hv.exists_of_le_one (hv.mem_of_integral hz)
  have hc : ‖algebraMap O C κ‖ ≤ (p : ℝ) ^ (-(1 / ((p : ℝ) - 1))) := by
    have hk : ‖algebraMap O C κ‖ ^ (p - 1) ≤ (p : ℝ)⁻¹ := by
      rw [← hps, hnorm, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), mul_comm,
        Real.rpow_mul (NNReal.coe_nonneg _), Real.rpow_natCast]
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hκ) hs.le
    have hx : ‖algebraMap O C κ‖ ^ ((p : ℝ) - 1) ≤ (p : ℝ)⁻¹ := by
      rw [show (p : ℝ) - 1 = ((p - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hpp.one_le, Nat.cast_one],
        Real.rpow_natCast]
      exact hk
    rw [one_div, Real.rpow_neg (by linarith), ← Real.inv_rpow (by linarith)]
    exact (Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by positivity) (by linarith)).2 hx
  exact @dvd_mul_of_groupLike C nnf ult hac h0 p _ hpn O _ hA hinj h1 h2 hcl B _ _ _ _ _ q hq D hD
    hu κ hc a

end Renorm

section Level

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] [IsIntegrallyClosedIn O C]

theorem dvd_mul_of_dvd_dlog (hv : v.Integers O) (hp : v (p : C) < 1) (G : PDivGroup p O) (n : ℕ)
    (q : O) (hq : q ≠ 0) (hqn : q ∣ (p : O) ^ n) (φ : G.omega →ₗ[O] O)
    (hφ : ∀ χ : G.dual.Tate, q ∣ φ (dlog G χ)) (κ : O)
    (hκ : v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)) (w : G.omega) : q ∣ κ * φ w := by
  let I : Ideal O := Ideal.span {q}
  have hz : ∀ x : O, I.mkQ x = 0 → q ∣ x := fun x h =>
    Ideal.mem_span_singleton.1 ((Submodule.Quotient.mk_eq_zero I).1 h)
  have hz' : ∀ x : O, q ∣ x → I.mkQ x = 0 := fun x h =>
    (Submodule.Quotient.mk_eq_zero I).2 (Ideal.mem_span_singleton.2 h)
  let ψ0 : G.omega →ₗ[O] O ⧸ I := I.mkQ ∘ₗ φ
  have hker : LinearMap.ker (G.omegaLevel n) ≤ LinearMap.ker ψ0 := fun x hx => by
    obtain ⟨u, rfl⟩ := (G.omega_val_eq_zero_iff n x).1 hx
    rw [LinearMap.mem_ker]
    refine hz' _ ?_
    rw [map_smul, smul_eq_mul]
    exact hqn.mul_right _
  let e := (G.omegaLevel n).quotKerEquivOfSurjective (G.omegaLevel_surjective n)
  let ψ : Cot O (G.A n) →ₗ[O] O ⧸ I :=
    ((LinearMap.ker (G.omegaLevel n)).liftQ ψ0 hker) ∘ₗ e.symm.toLinearMap
  have hψ : ∀ x : G.omega, ψ (x.1 n) = I.mkQ (φ x) := fun x => by
    have h : e.symm (x.1 n) = Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker (G.omegaLevel n)).liftQ ψ0 hker (e.symm (x.1 n)) = _
    rw [h]
    rfl
  obtain ⟨D, hD⟩ := Module.projective_lifting_property I.mkQ
    (ψ ∘ₗ AugCot.d (counitAlgHom O (G.A n))) (Submodule.mkQ_surjective I)
  have hDa : ∀ a, I.mkQ (D a) = ψ (dUnit (R := O) a) := fun a => LinearMap.congr_fun hD a
  have hdm : ∀ a b, ψ (dUnit (R := O) (a * b)) =
      counit (R := O) a • ψ (dUnit (R := O) b) + counit (R := O) b • ψ (dUnit (R := O) a) := fun a b => by
    rw [dUnit, AugCot.d_mul, map_add (f := _), map_smul, map_smul]
    rfl
  have key := dvd_mul_of_groupLike_val v p O hv hp (G.A n) q hq D
    (fun a b => hz _ (by
      change I.mkQ (D (a * b) - counit (R := O) a • D b - counit (R := O) b • D a) = 0
      rw [map_sub, map_sub, map_smul, map_smul, hDa, hDa, hDa, hdm]
      abel))
    (fun u hu => hz _ (by
      obtain ⟨χ, hχ⟩ := G.dual.pt_surjective C n (evalPoint u hu)
      have h1 : charElem χ n = u := CartierDual.eq_of_forall_apply (R := O) fun f => by
        have hχ' : χ.pt n = evalPoint u hu := hχ
        rw [apply_charElem, hχ']
        rfl
      rw [hDa, ← h1, ← dlog_val, hψ]
      exact hz' _ (hφ χ)))
    κ hκ
  obtain ⟨a, ha⟩ := AugCot.d_surjective (counitAlgHom O (G.A n)) (w.1 n)
  have h3 : q ∣ D a - φ w := hz _ (by
    rw [map_sub, hDa, sub_eq_zero, ← hψ]
    exact congrArg ψ ha)
  have h4 := dvd_sub (key a) (h3.mul_left κ)
  simpa [mul_sub] using h4

end Level

end GlobalTheory.CompanionTheory.Ar.HT.CokerSharp

namespace GlobalTheory.CompanionTheory.Ar.HT

open CokerSharp

theorem coker_dlog_killed : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C]
    (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O)
    [Algebra ℤ_[p] O] (G : PDivGroup p O) [Module.Free O G.omega] [Module.Finite O G.omega] (κ : O),
    v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C) → ∀ w : G.omega,
      κ • w ∈ LinearMap.range (dlogLinear G) := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO _ G _ _ κ hκ w
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.dual.finite_tate C
  obtain ⟨m, t, ht⟩ := Module.Finite.exists_fin (R := ℤ_[p]) (M := G.dual.Tate)
  let g : Fin m → G.omega := fun k => dlog G (t k)
  obtain ⟨φ, e, d, h1, h2, h3, h4⟩ := exists_diag hv (Module.finBasis O G.omega) g
  have hspan : Submodule.span O (Set.range g) ≤ LinearMap.range (dlogLinear G) :=
    Submodule.span_le.2 (by
      rintro _ ⟨k, rfl⟩
      exact ⟨1 ⊗ₜ t k, by simp [g]⟩)
  by_cases hκ0 : κ = 0
  · rw [hκ0, zero_smul]
    exact zero_mem _
  have hpO : (p : O) ≠ 0 := fun h => by
    have h5 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h5
    exact Nat.cast_ne_zero.2 hpp.ne_zero h5
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ (p : O) ^ n ∣ κ := by
    by_contra hall
    push Not at hall
    refine hκ0 (hO.toIsHausdorff.haus' κ fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact hall n
  have hdlog : ∀ (j : Fin _) (q : O), (∀ k, q ∣ φ j (g k)) →
      ∀ χ : G.dual.Tate, q ∣ φ j (dlog G χ) := fun j q hk χ => by
    have hχ : χ ∈ Submodule.span ℤ_[p] (Set.range t) := ht ▸ Submodule.mem_top
    induction hχ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact hk k
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add (f := _), map_add (f := _)]
      exact dvd_add hx hy
    | smul a x _ hx =>
      rw [dlog_smul (algebraMap ℤ_[p] O), map_smul, smul_eq_mul]
      exact hx.mul_left _
  have key : ∀ j, κ • e j ∈ LinearMap.range (dlogLinear G) := fun j => by
    rcases le_total (v (algebraMap O C ((p : O) ^ n))) (v (algebraMap O C (d j))) with h | h
    · have hd : d j ∣ (p : O) ^ n := hv.dvd_of_le h
      have hd0 : d j ≠ 0 := fun h0 => pow_ne_zero n hpO (zero_dvd_iff.1 (h0 ▸ hd))
      have h5 := dvd_mul_of_dvd_dlog hv hp G n (d j) hd0 hd (φ j) (hdlog j _ (h3 j)) κ hκ (e j)
      rw [h1, mul_one] at h5
      obtain ⟨c, hc⟩ := h5
      rw [hc, mul_comm, mul_smul]
      exact Submodule.smul_mem _ _ (hspan (h4 j))
    · have hd : (p : O) ^ n ∣ d j := hv.dvd_of_le h
      have h5 := dvd_mul_of_dvd_dlog hv hp G n ((p : O) ^ n) (pow_ne_zero n hpO) dvd_rfl (φ j)
        (hdlog j _ fun k => hd.trans (h3 j k)) κ hκ (e j)
      rw [h1, mul_one] at h5
      exact absurd h5 hn
  rw [h2 w, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_comm]
  exact Submodule.smul_mem _ _ (key j)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

noncomputable section

open CategoryTheory TensorProduct GlobalTheory GlobalTheory.PDivGroup WithConv

namespace GlobalTheory.CompanionTheory.Ar.HT.Lagr

section Rank

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_smul_mem {Q : Type} [AddCommGroup Q] [Module O Q]
    (hQ : Module.rank O Q < Cardinal.aleph0) (P : Submodule O Q)
    (h : Module.finrank O Q ≤ Module.finrank O P) (y : Q) : ∃ a : O, a ≠ 0 ∧ a • y ∈ P := by
  have hP : Module.rank O P < Cardinal.aleph0 := (Submodule.rank_le P).trans_lt hQ
  have h1 := HasRankNullity.rank_quotient_add_rank P
  have h2 : Module.rank O P = Module.rank O Q := by
    refine le_antisymm (Submodule.rank_le P) ?_
    rw [← Cardinal.cast_toNat_of_lt_aleph0 hQ, ← Cardinal.cast_toNat_of_lt_aleph0 hP]
    exact Nat.cast_le.2 h
  have h3 : Module.rank O (Q ⧸ P) = 0 := by
    refine Cardinal.eq_of_add_eq_add_right (b := Module.rank O P) ?_ hP
    rw [h1, h2, zero_add]
  obtain ⟨a, ha, hy⟩ := rank_eq_zero_iff.1 h3 (Submodule.Quotient.mk y)
  exact ⟨a, ha, (Submodule.Quotient.mk_eq_zero P).1 (by rw [Submodule.Quotient.mk_smul]; exact hy)⟩

variable {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M]

theorem finrank_range_add_ker {M' : Type} [AddCommGroup M'] [Module O M'] (f : M →ₗ[O] M') :
    Module.finrank O (LinearMap.range f) + Module.finrank O (LinearMap.ker f) =
      Module.finrank O M := by
  have h1 : Module.rank O (LinearMap.range f) < Cardinal.aleph0 := Module.rank_lt_aleph0 O _
  have h2 : Module.rank O (LinearMap.ker f) < Cardinal.aleph0 :=
    (Submodule.rank_le _).trans_lt (Module.rank_lt_aleph0 O M)
  have h3 := congrArg Cardinal.toNat (LinearMap.rank_range_add_rank_ker f)
  rwa [Cardinal.toNat_add h1 h2] at h3

theorem finrank_le_add (B : M →ₗ[O] M →ₗ[O] O) (W N : Submodule O M)
    (hN : ∀ x, x ∈ N ↔ ∀ y ∈ W, B x y = 0) :
    Module.finrank O M ≤ Module.finrank O W + Module.finrank O N := by
  have hWr : Module.rank O W < Cardinal.aleph0 :=
    (Submodule.rank_le W).trans_lt (Module.rank_lt_aleph0 O M)
  obtain ⟨w, hw⟩ := exists_linearIndependent_of_le_finrank (R := O) (M := W) le_rfl
  let S : Submodule O W := Submodule.span O (Set.range w)
  have hS : Module.finrank O W ≤ Module.finrank O S := by
    rw [finrank_span_eq_card hw, Fintype.card_fin]
  let Φ : M →ₗ[O] (Fin (Module.finrank O W) → O) := LinearMap.pi fun j => B.flip (w j : M)
  have hker : LinearMap.ker Φ = N := by
    ext x
    rw [hN, LinearMap.mem_ker]
    constructor
    · intro hx y hy
      obtain ⟨a, ha, hay⟩ := exists_smul_mem hWr S hS ⟨y, hy⟩
      have h0 : ∀ s ∈ S, B x (s : M) = 0 := fun s hs => by
        induction hs using Submodule.span_induction with
        | mem s hs =>
          obtain ⟨j, rfl⟩ := hs
          exact congrFun hx j
        | zero => simp
        | add s t _ _ hs ht => simp [hs, ht]
        | smul c s _ hs => simp [hs]
      have h1 := h0 _ hay
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left ha
    · intro hx
      exact funext fun j => hx _ (w j).2
  have h1 := finrank_range_add_ker Φ
  have h2 : Module.finrank O (LinearMap.range Φ) ≤ Module.finrank O W := by
    have := Submodule.finrank_le (LinearMap.range Φ)
    simpa using this
  rw [hker] at h1
  omega

theorem le_of_finrank (B : M →ₗ[O] M →ₗ[O] O) (W N : Submodule O M)
    (hN : ∀ x, x ∈ N ↔ ∀ y ∈ W, B x y = 0) (hNW : N ≤ W)
    (hr : 2 * Module.finrank O W ≤ Module.finrank O M) : W ≤ N := by
  have hWr : Module.rank O W < Cardinal.aleph0 :=
    (Submodule.rank_le W).trans_lt (Module.rank_lt_aleph0 O M)
  have h1 := finrank_le_add B W N hN
  let P : Submodule O W := N.comap W.subtype
  have hP : Module.finrank O W ≤ Module.finrank O P := by
    have : Module.finrank O P = Module.finrank O N :=
      (Submodule.comapSubtypeEquivOfLe hNW).finrank_eq
    omega
  intro x hx
  obtain ⟨a, ha, hax⟩ := exists_smul_mem hWr P hP ⟨x, hx⟩
  rw [hN]
  intro y hy
  have h2 : a • x ∈ N := hax
  have h3 := (hN _).1 h2 y hy
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left ha

end Rank

section Tate

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

theorem charElem_bidual (G : PDivGroup p O) (t : G.Tate) (n : ℕ) :
    charElem (G := G.dual) (tateMap G G.dual.dual O G.bidual.hom t) n =
      toConv (t.pt n).toLinearMap :=
  (charHom_app_muT _ n).symm.trans (dualChar_app_muT t n)

theorem pairing_dual_bidual (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    pairing G.dual O χ (tateMap G G.dual.dual O G.bidual.hom t) = pairing G O t χ :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing, charElem_bidual]
    exact (apply_charElem χ n _).symm

theorem algebraMap_injective [IsDomain O] [Algebra ℤ_[p] O] (hp : (p : O) ≠ 0) :
    Function.Injective (algebraMap ℤ_[p] O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h
  have h2 := congrArg (algebraMap ℤ_[p] O) (PadicInt.unitCoeff_spec h)
  rw [ha, map_mul, map_pow, map_natCast] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact ((PadicInt.unitCoeff h).isUnit.map (algebraMap ℤ_[p] O)).ne_zero h3
  · exact pow_ne_zero _ hp h3

theorem tateMap_dualHom_bidual (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C]
    [IsAlgClosed C] [CharZero C] [IsDomain O] [Algebra ℤ_[p] O] (hp : (p : O) ≠ 0)
    (G : PDivGroup p O) (lam : G ⟶ G.dual) (μ : (mu p O).Tate)
    (B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.Tate →ₗ[O] O)
    (hB : ∀ x y : G.Tate, ∃ a : ℤ_[p], pairing G O y (tateMap G G.dual O lam x) = a • μ ∧
      B (1 ⊗ₜ x) (1 ⊗ₜ y) = algebraMap ℤ_[p] O a)
    (hskew : ∀ x y, B x y = - B y x) (t : G.Tate) :
    tateMap _ _ O (dualHom G G.dual lam) (tateMap G G.dual.dual O G.bidual.hom t) =
      - tateMap G G.dual O lam t := by
  refine (G.pairing_flip_bijective C).1 (LinearMap.ext fun y => ?_)
  change pairing G O y _ = pairing G O y _
  rw [← pairing_tateMap, pairing_dual_bidual, map_neg]
  obtain ⟨a, ha, hb⟩ := hB y t
  obtain ⟨a', ha', hb'⟩ := hB t y
  have h : a = - a' := algebraMap_injective hp (by rw [map_neg, ← hb, ← hb', hskew])
  rw [ha, ha', h, neg_smul]

end Tate

end GlobalTheory.CompanionTheory.Ar.HT.Lagr

namespace GlobalTheory.CompanionTheory.Ar.HT

open AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField GlobalTheory.CompanionTheory.Ar
  GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi Lagr

theorem dlog_lagrangian : FarguesHodgeTate → ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) [Algebra ℤ_[p] O] (G : PDivGroup p O) [Module.Free O G.omega] [Module.Finite O G.omega] (lam : G ⟶ G.dual) (ζ : ℕ → O) (h0 : ζ 0 = 1) (h : ∀ n, ζ (n + 1) ^ p = ζ n) (B : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.Tate →ₗ[O] O) (κ : O), ζ 1 ≠ 1 → IsHTConst v p κ → Function.Bijective (tateMap G G.dual O lam) → 2 * Module.finrank O G.omega = G.height → (∀ x y : G.Tate, ∃ a : ℤ_[p], pairing G O y (tateMap G G.dual O lam x) = a • muTate O ζ h0 h ∧ B (1 ⊗ₜ x) (1 ⊗ₜ y) = algebraMap ℤ_[p] O a) → (∀ x, B x x = 0) → (∀ w : G.omega, κ • w ∈ LinearMap.range (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O)) ∧ ∀ x, (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O) x = 0 ↔ ∀ y, (dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O) y = 0 → B x y = 0 := by
  intro hF p _ C _ _ _ v O _ _ _ hv hp hO _ G _ _ lam ζ h0 h B κ hζ hκ hbij hdim hB halt
  have hpp : p.Prime := Fact.out
  have : IsIntegrallyClosedIn O C := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.mem_of_integral hx)⟩
  have := G.finite_tate C
  have := G.free_tate C
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h5 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h5
    exact Nat.cast_ne_zero.2 hpp.ne_zero h5
  have hκ0 : κ ≠ 0 := fun h => hκ.1 (by rw [h, map_zero])
  have hskew : ∀ x y, B x y = - B y x := fun x y => by
    have h1 := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt, zero_add, add_zero] at h1
    exact eq_neg_of_add_eq_zero_right h1
  let e : G.Tate ≃ₗ[ℤ_[p]] G.dual.Tate := LinearEquiv.ofBijective _ hbij
  let L : O ⊗[ℤ_[p]] G.Tate ≃ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate := e.baseChange ℤ_[p] O _ _
  have hL : ∀ x, (tateMap G G.dual O lam).baseChange O x = L x := fun _ => rfl
  set f := dlogLinear G ∘ₗ (tateMap G G.dual O lam).baseChange O with hf
  have hfL : ∀ x, f x = dlogLinear G (L x) := fun _ => rfl
  have hcoker : ∀ w : G.omega, κ • w ∈ LinearMap.range f := fun w => by
    obtain ⟨u, hu⟩ := coker_dlog_killed p C v O hv hp hO G κ hκ.2 w
    exact ⟨L.symm u, by rw [hfL, L.apply_symm_apply, hu]⟩
  refine ⟨hcoker, ?_⟩

  let B' : O ⊗[ℤ_[p]] G.Tate →ₗ[O] O ⊗[ℤ_[p]] G.dual.Tate →ₗ[O] O :=
    (B ∘ₗ L.symm.toLinearMap).flip
  have hB' : ∀ (x : G.Tate) (χ : G.dual.Tate), ∃ a : ℤ_[p],
      pairing G O x χ = a • muTate O ζ h0 h ∧ B' (1 ⊗ₜ x) (1 ⊗ₜ χ) = algebraMap ℤ_[p] O a := by
    intro x χ
    obtain ⟨z, rfl⟩ := hbij.2 χ
    obtain ⟨a, ha, hb⟩ := hB z x
    refine ⟨a, ha, ?_⟩
    have h1 : L.symm (1 ⊗ₜ tateMap G G.dual O lam z) = 1 ⊗ₜ z := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change B (L.symm _) _ = _
    rw [h1, hb]
  have hN : ∀ x, x ∈ LinearMap.ker (hodgeTateLinear G) ↔
      ∀ y ∈ LinearMap.ker f, B x y = 0 := by
    intro x
    rw [LinearMap.mem_ker, (hF p C v O hv hp hO G).2 ζ h0 h hζ B' hB' x]
    constructor
    · intro hx y hy
      have h1 := hx (L y) hy
      have h2 : B y x = 0 := by
        have : B' x (L y) = B y x := by
          change B (L.symm (L y)) x = _
          rw [L.symm_apply_apply]
        rwa [this] at h1
      rw [hskew, h2, neg_zero]
    · intro hx y hy
      have h1 := hx (L.symm y) (by
        rw [LinearMap.mem_ker, hfL, L.apply_symm_apply]
        exact hy)
      change B (L.symm y) x = 0
      rw [hskew, h1, neg_zero]

  have hkey : ∀ x, omegaMap G G.dual lam (hodgeTateLinear G x) = - f x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), neg_add]
    | tmul c t =>
      have h1 : omegaMap G G.dual lam (hodgeTate G t) = - dlog G (tateMap G G.dual O lam t) := by
        rw [hodgeTate_apply, ← dlog_tateMap,
          tateMap_dualHom_bidual C hp0 G lam (muTate O ζ h0 h) B hB hskew, map_neg]
      have h2 : f (c ⊗ₜ t) = c • dlog G (tateMap G G.dual O lam t) := rfl
      rw [hodgeTateLinear_tmul, map_smul, h1, h2, smul_neg]
  have hNW : LinearMap.ker (hodgeTateLinear G) ≤ LinearMap.ker f := fun x hx => by
    have h1 := hkey x
    rw [LinearMap.mem_ker.1 hx, map_zero] at h1
    exact LinearMap.mem_ker.2 (neg_eq_zero.1 h1.symm)

  have hM : Module.finrank O (O ⊗[ℤ_[p]] G.Tate) = G.height := by
    rw [Module.finrank_baseChange, G.finrank_tate C]
  let g : G.omega →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict _ (κ • LinearMap.id) hcoker
  have hg : Function.Injective g := fun a b hab => by
    have h1 : κ • a = κ • b := congrArg Subtype.val hab
    exact smul_right_injective _ hκ0 h1
  have h1 := LinearMap.finrank_le_finrank_of_injective hg
  have h2 := (finrank_range_add_ker f).trans hM
  have h3 : 2 * Module.finrank O (LinearMap.ker f) ≤ G.height := by
    omega
  have hWN := le_of_finrank B (LinearMap.ker f) _ hN hNW (h3.trans_eq hM.symm)
  intro x
  constructor
  · intro hx y hy
    exact (hN x).1 (hWN hx) y hy
  · intro hx
    exact hNW ((hN x).2 hx)

end GlobalTheory.CompanionTheory.Ar.HT
