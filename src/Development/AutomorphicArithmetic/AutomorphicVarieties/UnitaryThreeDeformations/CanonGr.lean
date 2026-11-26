module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section
open LaurentPolynomial

private theorem exists_coact {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] :
    ∃ φ : R →+* R[T;T⁻¹], ∀ (j : ℤ) (x : R), x ∈ 𝒜 j ↔ φ x = C x * T j := by
  let t : Multiplicative ℤ →* (R[T;T⁻¹])ˣ := (AddMonoidAlgebra.of R ℤ).toHomUnits
  let φ : R →ₐ[O] R[T;T⁻¹] := act 𝒜 t (IsScalarTower.toAlgHom O R R[T;T⁻¹])
  have h1 : ∀ j x, x ∈ 𝒜 j → φ x = C x * T j := fun j x hx => by
    rw [mul_comm]
    exact act_of_mem 𝒜 t _ hx
  have h2 : ∀ x j, (φ x).coeff j = (DirectSum.decompose 𝒜 x j : R) := by
    intro x j
    induction x using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous i m =>
      rw [h1 i m m.2, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single]
      by_cases hij : i = j
      · subst hij
        rw [DirectSum.decompose_of_mem_same 𝒜 m.2, Finsupp.single_eq_same]
      · rw [DirectSum.decompose_of_mem_ne 𝒜 m.2 hij, Finsupp.single_eq_of_ne' hij]
    | add a b ha hb => simp [ha, hb]
  refine ⟨φ, fun j x => ⟨h1 j x, fun hx => ?_⟩⟩
  have h3 := h2 x j
  have hx' : φ x = C x * T j := hx
  rw [hx', ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] at h3
  rw [h3]
  exact Subtype.property _

private theorem eig_unique {S n : Type} [CommRing S] [Fintype n] [DecidableEq n]
    (X h g h' : Matrix n n S) (l l' : n → S) (hg : h * g = 1) (gh : g * h = 1)
    (e : X * h = h * diagonal l) (e' : X * h' = h' * diagonal l')
    (o : ∀ a, h a a = 1) (o' : ∀ a, h' a a = 1) (u : ∀ a b, a ≠ b → IsUnit (l a - l' b)) : h' = h := by
  have e1 : g * X = diagonal l * g := by
    calc g * X = g * (X * h) * g := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hg, Matrix.mul_one]
      _ = _ := by rw [e, ← Matrix.mul_assoc, gh, Matrix.one_mul]
  have e2 : diagonal l * (g * h') = (g * h') * diagonal l' := by
    rw [← Matrix.mul_assoc, ← e1, Matrix.mul_assoc, e', Matrix.mul_assoc]
  have e3 : (g * h').IsDiag := by
    intro a b hab
    have := congrFun (congrFun e2 a) b
    rw [diagonal_mul, mul_diagonal] at this
    exact (u a b hab).mul_right_eq_zero.1 (by rw [sub_mul, this]; ring)
  have e4 : h' = h * diagonal (diag (g * h')) := by
    rw [e3.diagonal_diag, ← Matrix.mul_assoc, hg, Matrix.one_mul]
  have e5 : diag (g * h') = fun _ => 1 := by
    funext a
    have := congrFun (congrFun e4 a) a
    rw [mul_diagonal, o, o', one_mul] at this
    exact this.symm
  rw [e4, e5, diagonal_one, Matrix.mul_one]

end

open LaurentPolynomial in
theorem UpperTheory.V.UnitaryThreeInertia.canon_graded :
    ∀ {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [Finite R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (X : Matrix (Fin 3) (Fin 3) R) (h : GL (Fin 3) R), (∀ a b, a ≠ b → IsUnit (X a a - X b b)) → GrMat 𝒜 X → Canon X h → GrMat 𝒜 h.val ∧ GrMat 𝒜 (h⁻¹).val := by
  intro O R _ _ _ _ _ _ 𝒜 _ X h hu hX hc
  obtain ⟨φ, hφ⟩ := exists_coact 𝒜
  have hnil : ∀ x ∈ maximalIdeal R, IsNilpotent x := by
    intro x hx
    obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
    refine ⟨n, ?_⟩
    have := Ideal.pow_mem_pow hx n
    rw [hn] at this
    exact this
  set l : Fin 3 → R := diag ((h⁻¹).val * X * h.val) with hl
  have e : X * h.val = h.val * diagonal l := by
    rw [hl, hc.diag.diagonal_diag, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hlX : ∀ a, IsNilpotent (l a - X a a) := by
    intro a
    apply hnil
    have e1 : X * (h.val - 1) = h.val * diagonal l - X := by rw [Matrix.mul_sub, e, Matrix.mul_one]
    have e2 := congrFun (congrFun e1 a) a
    rw [Matrix.sub_apply, mul_diagonal, hc.one, one_mul] at e2
    rw [← e2, Matrix.mul_apply]
    exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hc.hat c a)
  let D : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (wt1 a)
  let D' : Matrix (Fin 3) (Fin 3) R[T;T⁻¹] := diagonal fun a => T (-wt1 a)
  have DD : D * D' = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, add_neg_cancel, T_zero, diagonal_one]
  have DD' : D' * D = 1 := by
    simp only [D, D', diagonal_mul_diagonal, ← T_add, neg_add_cancel, T_zero, diagonal_one]
  have ent : ∀ (M : Matrix (Fin 3) (Fin 3) R[T;T⁻¹]) a b, (D * M * D') a b = M a b * T (wt a b) := by
    intro M a b
    simp only [D, D', mul_diagonal, diagonal_mul, wt, T_sub]
    ring
  have key : ∀ M : Matrix (Fin 3) (Fin 3) R, GrMat 𝒜 M ↔ M.map φ = D * M.map C * D' := by
    intro M
    constructor
    · intro hM
      ext1 a b
      rw [ent]
      exact (hφ _ _).1 (hM a b)
    · intro hM a b
      have := congrFun (congrFun hM a) b
      rw [ent] at this
      exact (hφ _ _).2 this
  have inv1 : ∀ f : R →+* R[T;T⁻¹], h.val.map f * (h⁻¹).val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one f (map_zero f) (map_one f)]
  have inv2 : ∀ f : R →+* R[T;T⁻¹], (h⁻¹).val.map f * h.val.map f = 1 := fun f => by
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one f (map_zero f) (map_one f)]
  have emap : ∀ f : R →+* R[T;T⁻¹], X.map f * h.val.map f = h.val.map f * diagonal fun a => f (l a) := fun f => by
    rw [← Matrix.map_mul, e, Matrix.map_mul, diagonal_map (map_zero f)]
  have can : ∀ M N : Matrix (Fin 3) (Fin 3) R[T;T⁻¹], (D * M * D') * (D * N * D') = D * (M * N) * D' := by
    intro M N
    calc _ = D * M * (D' * D) * N * D' := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [DD', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have main : D * h.val.map C * D' = h.val.map φ := by
    refine eig_unique (X.map φ) (h.val.map φ) ((h⁻¹).val.map φ) _ (fun a => φ (l a)) (fun a => C (l a))
      (inv1 φ) (inv2 φ) (emap φ) ?_ (fun a => by simp [hc.one]) (fun a => by rw [ent]; simp [hc.one, wt]) ?_
    · rw [(key X).1 hX, can, emap C]
      have hcomm : (diagonal fun a => C (l a)) * D' = D' * diagonal fun a => C (l a) := by
        simp only [D', diagonal_mul_diagonal, mul_comm]
      simp only [Matrix.mul_assoc]
      rw [hcomm]
    · intro a b hab
      have hXa : φ (X a a) = C (X a a) := by
        have := (hφ _ _).1 (hX a a)
        simpa [wt] using this
      have h1 : IsNilpotent (φ (l a - X a a) - C (l b - X b b)) :=
        (Commute.all _ _).isNilpotent_sub ((hlX a).map φ) ((hlX b).map C)
      have h2 := h1.isUnit_add_right_of_commute ((hu a b hab).map C) (Commute.all _ _)
      convert h2 using 1
      simp only [map_sub, hXa]
      ring
  refine ⟨(key _).2 main.symm, (key _).2 ?_⟩
  have h3 : h.val.map φ * (D * (h⁻¹).val.map C * D') = 1 := by
    rw [← main, can, inv1, Matrix.mul_one, DD]
  calc (h⁻¹).val.map φ = (h⁻¹).val.map φ * (h.val.map φ * (D * (h⁻¹).val.map C * D')) := by
        rw [h3, Matrix.mul_one]
    _ = _ := by rw [← Matrix.mul_assoc, inv2, Matrix.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TriangularConditionAtLOfFirstOrderDeformation
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] {m : Ideal R}

private def Kil (m : Ideal R) (X : Matrix (Fin 3) (Fin 3) R) : Prop := ∀ a b, ∀ x ∈ m, x * X a b = 0

private theorem kil_left {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : M * X = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => hX c b _ (hM a c)

private theorem kil_right {X M : Matrix (Fin 3) (Fin 3) R} (hX : Kil m X) (hM : EntIn m M) : X * M = 0 := by
  ext a b
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun c _ => by rw [mul_comm]; exact hX a c _ (hM c b)

private theorem ent_left {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (N * M) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_left _ _ (hM c b)

private theorem ent_right {M : Matrix (Fin 3) (Fin 3) R} (N : Matrix (Fin 3) (Fin 3) R) (hM : EntIn m M) :
    EntIn m (M * N) := fun a b => by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_right _ _ (hM a c)

private theorem core {h hi A D Y γ : Matrix (Fin 3) (Fin 3) R} (hh : EntIn m (h - 1)) (hhi : EntIn m (hi - 1))
    (hA : EntIn m (A - D)) (hY : Kil m Y) (hYm : EntIn m Y) (hγ : Kil m γ) :
    hi * (1 + Y) * ((1 + γ) * A) * ((1 - Y) * h) = hi * A * h + (Y * D + γ * D - D * Y) := by
  obtain ⟨p, rfl⟩ : ∃ p, h = 1 + p := ⟨h - 1, by abel⟩
  obtain ⟨q, rfl⟩ : ∃ q, hi = 1 + q := ⟨hi - 1, by abel⟩
  obtain ⟨e, rfl⟩ : ∃ e, A = D + e := ⟨A - D, by abel⟩
  simp only [add_sub_cancel_left] at hh hhi hA
  have e1 : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) := by
    have a1 : Y * γ = 0 := kil_left hγ hYm
    have a2 : Y * e = 0 := kil_right hY hA
    have a3 : γ * e = 0 := kil_right hγ hA
    have a4 : e * Y = 0 := kil_left hY hA
    have a5 : Y * (D * Y) = 0 := kil_right hY (ent_left _ hYm)
    have a6 : γ * (D * Y) = 0 := kil_right hγ (ent_left _ hYm)
    have : (1 + Y) * ((1 + γ) * (D + e)) * (1 - Y) = (D + e) + (Y * D + γ * D - D * Y) +
        ((Y * γ) * (D + e) * (1 - Y) + (Y * e) * (1 - Y) + (γ * e) * (1 - Y) - e * Y - Y * (D * Y) - γ * (D * Y)) := by
      noncomm_ring
    rw [this, a1, a2, a3, a4, a5, a6]; simp
  have hW : Kil m (Y * D + γ * D - D * Y) := fun a b x hx => by
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, mul_sub, mul_add, Finset.mul_sum,
      ← mul_assoc, hY _ _ x hx, hγ _ _ x hx, zero_mul, hY _ _ _ (Ideal.mul_mem_right _ _ hx)]
    simp
  generalize Y * D + γ * D - D * Y = W at e1 hW
  have b1 : q * W = 0 := kil_left hW hhi
  have b2 : W * p = 0 := kil_right hW hh
  calc _ = (1 + q) * ((1 + Y) * ((1 + γ) * (D + e)) * (1 - Y)) * (1 + p) := by simp only [Matrix.mul_assoc]
    _ = (1 + q) * (D + e) * (1 + p) + W + ((q * W) * (1 + p) + W * p) := by rw [e1]; noncomm_ring
    _ = _ := by rw [b1, b2]; simp

private theorem conj_mat {D : Type} [Group D] (h : GL (Fin 3) R) (r : D →* GG (m := 3) (R := R)) (g : D) (hg : (r g).right = 1) :
    (conjBy h⁻¹ r g).mat = ((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * (r g).mat * h := by
  simp [conjBy, GG.mat, hg]

private theorem ad_entry {D k : Type} [Group D] [CommRing k] (η : D →* ℤˣ) (Ψ : D →* kˣ) (g : D) (hg : η g = 1)
    (X : Matrix (Fin 3) (Fin 3) k) (a b : Fin 3) :
    adRep (r0 η Ψ) g X a b * ((Ψ g ^ wt1 b : kˣ) : k) = ((Ψ g ^ wt1 a : kˣ) : k) * X a b := by
  show (GG.adFun (r0 η Ψ g) X) a b * _ = _
  unfold GG.adFun GG.mat
  rw [unitaryThreeReflection_left, ← map_inv, tor_val, tor_val, Matrix.mul_diagonal, Matrix.diagonal_mul, unitaryThreeReflection_right, if_pos hg,
    mul_assoc, ← Units.val_mul, ← mul_zpow]
  simp

private theorem condT_deform {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [Algebra O R] [IsCO O R]
    (η : D →* ℤˣ) (Ψ : D →* Oˣ) (I : Subgroup D) (f : R) (hf : ∀ x ∈ maximalIdeal R, x * f = 0)
    (hfm : f ∈ maximalIdeal R) (r r₂ : D →* GG (m := 3) (R := R)) (z : D → Matrix (Fin 3) (Fin 3) (ResidueField O))
    (γ : D → Matrix (Fin 3) (Fin 3) R) (hr : Red η Ψ r) (ht : CondT η Ψ I r)
    (hγ : ∀ g a b, ∃ o : O, residue O o = z g a b ∧ γ g a b = o • f) (hd : IsDeform r γ r₂)
    (μ : Matrix (Fin 3) (Fin 3) (ResidueField O))
    (h1 : ∀ g, η g = 1 → ∀ a b, wt a b < 0 →
      μ a b * residue O (psi Ψ b g) + z g a b * residue O (psi Ψ b g) - residue O (psi Ψ a g) * μ a b = 0)
    (h2 : ∀ s ∈ I, ∀ a, z s a a = 0) : CondT η Ψ I r₂ := by
  obtain ⟨h, hh, htri, hine⟩ := ht
  have hk : ∀ o : O, ∀ x ∈ maximalIdeal R, x * (o • f) = 0 := fun o x hx => by
    rw [mul_smul_comm, hf x hx, smul_zero]
  have h0 : ∀ o : O, residue O o = 0 → o • f = 0 := fun o ho => by
    rw [Algebra.smul_def]
    exact hf _ (map_nonunit (algebraMap O R) o ((residue_eq_zero_iff _).1 ho))
  choose o ho using fun a b => residue_surjective (μ a b)
  let Y : Matrix (Fin 3) (Fin 3) R := Matrix.of fun a b => o a b • f
  have hY : Kil (maximalIdeal R) Y := fun a b => hk _
  have hYm : EntIn (maximalIdeal R) Y := fun a b => Submodule.smul_of_tower_mem _ _ hfm
  have hYY : Y * Y = 0 := kil_left hY hYm
  let u : GL (Fin 3) R := ⟨1 - Y, 1 + Y,
    by rw [show (1 - Y) * (1 + Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero],
    by rw [show (1 + Y) * (1 - Y) = 1 - Y * Y by noncomm_ring, hYY, sub_zero]⟩
  have hhi : EntIn (maximalIdeal R) (((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1) := by
    have := ent_left (-((h⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) hh
    rwa [Matrix.mul_sub, Matrix.neg_mul, Units.inv_mul, Matrix.mul_one, sub_neg_eq_add, neg_add_eq_sub] at this
  have key : ∀ g, η g = 1 → ∀ a b, ∃ c : O, residue O c = z g a b ∧ (conjBy (u * h)⁻¹ r₂ g).mat a b =
      (conjBy h⁻¹ r g).mat a b + (o a b * psi Ψ b g + c * psi Ψ b g - psi Ψ a g * o a b) • f := by
    intro g hg a b
    obtain ⟨c, hc, hc'⟩ := hγ g a b
    refine ⟨c, hc, ?_⟩
    have hrg : (r g).right = 1 := (hr.mult g).trans hg
    have hγk : Kil (maximalIdeal R) (γ g) := fun a b => by
      obtain ⟨c, -, hc'⟩ := hγ g a b
      rw [hc']; exact hk c
    have hD : ((r0 η Ψ g).mat).map (algebraMap O R) = Matrix.diagonal fun a => algebraMap O R (psi Ψ a g) := by
      unfold GG.mat
      rw [unitaryThreeReflection_left, tor_val, Matrix.diagonal_map (map_zero _)]
      rfl
    have hA := hr.red g
    rw [hD] at hA
    have := core hh hhi hA hY hYm hγk
    rw [conj_mat _ _ _ hrg, conj_mat _ _ _ ((hd g).1.trans hrg), (hd g).2, _root_.mul_inv_rev, Units.val_mul,
      Units.val_mul]
    refine (congrFun (congrFun this a) b).trans ?_
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hc', Y,
      Matrix.of_apply, Algebra.smul_def, map_sub, map_add, map_mul]
    ring
  refine ⟨u * h, ?_, fun g hg a b hab => ?_, fun s hs hη a => ?_⟩
  · have e : ((u * h : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) - 1 = ((h : Matrix (Fin 3) (Fin 3) R) - 1) - Y * h := by
      show (1 - Y) * (h : Matrix (Fin 3) (Fin 3) R) - 1 = _
      noncomm_ring
    intro a b
    rw [e, Matrix.sub_apply]
    exact Ideal.sub_mem _ (hh a b) (ent_right _ hYm a b)
  · obtain ⟨c, hc, e⟩ := key g hg a b
    rw [e, htri g hg a b hab, zero_add]
    apply h0
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, ho, hc]
    exact h1 g hg a b hab
  · obtain ⟨c, hc, e⟩ := key s hη a a
    rw [e, hine s hs hη a, h0, add_zero]
    rw [map_sub, map_add (f := _), map_mul, map_mul, map_mul, hc, h2 s hs a]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.V.UnitaryThreeInertia.triangular_condition_at_l_of_first_order_deformation :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (f : R), (∀ x ∈ maximalIdeal R, x * f = 0) → f ∈ maximalIdeal R → ∀ (j : ℤ) (v : ι), v = F.vl →
      ∀ (r r₂ : F.D v →* GG (m := 3) (R := R)) (z : F.D v → Gb (k := ResidueField O) j) (γ : F.D v → Matrix (Fin 3) (Fin 3) R), Red (F.ηv v) (F.Ψv v) r → F.LocAt v r →
      z ∈ F.ZL j v → (∀ g a b, ∃ o : O, residue O o = (z g).val a b ∧ γ g a b = o • f) → IsDeform r γ r₂ → F.LocAt v r₂ := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R _ _ _ f hf hfm j v hv r r₂ z γ hr hl hz hγ hd
  refine ⟨fun _ => ?_, fun h => absurd (hv ▸ h) hF.vl_notMem, fun h => absurd (Set.mem_insert_iff.2 (Or.inl hv)) h⟩
  have hw : ∀ (X : Gb (k := ResidueField O) j) a b, wt a b ≠ j → X.val a b = 0 := fun X => Subtype.property X
  have h2 : ∀ s ∈ F.Iv v, ∀ a, (z s).val a a = 0 := fun s hs a => by
    by_cases hj : j = 0
    · rw [hz.2.2.2 hv hj s hs]; rfl
    · exact hw _ _ _ (by simpa [wt] using Ne.symm hj)
  by_cases hj : j < 0
  · obtain ⟨μ, hμ⟩ := (mem_coboundaries1 _ _).1 (hz.2.2.1 hv hj)
    refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd μ.val ?_ h2
    intro g hg a b _
    have e : (z g).val a b = adRep (r0 F.η F.Ψbar) (F.loc v g) μ.val a b - μ.val a b := by
      rw [hμ g]; rfl
    have hp : ∀ a, residue O (psi (F.Ψv v) a g) = ((F.Ψbar (F.loc v g) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O) :=
      fun a => by
        show _ = ((Units.map (residue O).toMonoidHom (F.Ψ (F.loc v g)) ^ wt1 a : (ResidueField O)ˣ) : ResidueField O)
        rw [← map_zpow]; rfl
    have := ad_entry F.η F.Ψbar (F.loc v g) hg μ.val a b
    simp only [e, hp]
    linear_combination this
  · refine condT_deform _ _ _ f hf hfm r r₂ (fun g => (z g).val) γ hr (hl.1 hv) hγ hd 0 ?_ h2
    intro g _ a b hab
    simp [hw (z g) a b (by omega)]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CondConj
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ThetaInvolution
noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.Jmat.{u_1} :
    (R : Type u_1) → [CommRing R] → (m : ℕ) → Matrix (Fin m) (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) (i j : Fin m) ↦ if j = i.rev then (1 : R) else (0 : R)

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux2.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (m : ℕ),
      UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m * UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  intro R _ m
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [UpperTheory.Reformulated.B.ThetaInvolution.Jmat, Matrix.one_apply, if_true, one_mul, Fin.rev_rev]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun e => h e.symm), if_neg h]
  · intro k _ hk
    simp [UpperTheory.Reformulated.B.ThetaInvolution.Jmat, hk]
  · intro h; exact absurd (Finset.mem_univ _) h

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.Jgl.{u_1} :
    (R : Type u_1) → [inst : CommRing R] → (m : ℕ) → GL (Fin m) R :=
    fun (R : Type u_1) [CommRing R] (m : ℕ) ↦
      { val := UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m, inv := UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m, val_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux2 m,
        inv_val := UpperTheory.Reformulated.B.ThetaInvolution.aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux4.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux5.{u_1} :
    ∀ {n : Type} [inst : Fintype n] [inst_1 : DecidableEq n] {R : Type u_1} [inst_2 : CommRing R] (g : GL n R),
      (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  intro n _ _ R _ g
  rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.trInv.{u_1} :
    {n : Type} → [inst : Fintype n] → [inst_1 : DecidableEq n] → {R : Type u_1} → [inst_2 : CommRing R] → GL n R → GL n R :=
    fun {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) ↦
      { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose, val_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux4 g,
        inv_val := UpperTheory.Reformulated.B.ThetaInvolution.aux5 g : (Matrix n n R)ˣ }

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.theta.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R → GL (Fin m) R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) ↦
      UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.trInv g * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m

private theorem UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m = 1 :=
  Units.ext (UpperTheory.Reformulated.B.ThetaInvolution.aux2 m)

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g h : GL n R) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (g * h) = UpperTheory.Reformulated.B.ThetaInvolution.trInv g * UpperTheory.Reformulated.B.ThetaInvolution.trInv h := by
  apply Units.ext
  change (((g * h)⁻¹ : GL n R) : Matrix n n R).transpose =
    ((g⁻¹ : GL n R) : Matrix n n R).transpose * ((h⁻¹ : GL n R) : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_trInv.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1}
    [CommRing R] (g : GL n R) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (UpperTheory.Reformulated.B.ThetaInvolution.trInv g) = g := by
  apply Units.ext
  change (g : Matrix n n R).transpose.transpose = (g : Matrix n n R)
  exact Matrix.transpose_transpose _

private theorem UpperTheory.Reformulated.B.ThetaInvolution.trInv_Jgl.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) :
    UpperTheory.Reformulated.B.ThetaInvolution.trInv (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) = UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m := by
  apply Units.ext
  change (UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m).transpose = UpperTheory.Reformulated.B.ThetaInvolution.Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, UpperTheory.Reformulated.B.ThetaInvolution.Jmat]
  by_cases h : j = i.rev
  · rw [if_pos h, if_pos (by rw [h, Fin.rev_rev])]
  · rw [if_neg h, if_neg (fun e => h (by rw [e, Fin.rev_rev]))]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux8.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g : GL (Fin m) R), UpperTheory.Reformulated.B.ThetaInvolution.theta (UpperTheory.Reformulated.B.ThetaInvolution.theta g) = g := by
  intro m R _ g
  have hJ := UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self R m
  simp only [UpperTheory.Reformulated.B.ThetaInvolution.theta, UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul, UpperTheory.Reformulated.B.ThetaInvolution.trInv_trInv,
    UpperTheory.Reformulated.B.ThetaInvolution.trInv_Jgl]
  calc _ = (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) * g *
        (UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux9.{u_1} :
    ∀ {m : ℕ} {R : Type u_1} [inst : CommRing R] (g h : GL (Fin m) R),
      UpperTheory.Reformulated.B.ThetaInvolution.theta (g * h) = UpperTheory.Reformulated.B.ThetaInvolution.theta g * UpperTheory.Reformulated.B.ThetaInvolution.theta h := by
  intro m R _ g h
  have hJ := UpperTheory.Reformulated.B.ThetaInvolution.Jgl_mul_self R m
  simp only [UpperTheory.Reformulated.B.ThetaInvolution.theta, UpperTheory.Reformulated.B.ThetaInvolution.trInv_mul]
  calc _ = UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m * UpperTheory.Reformulated.B.ThetaInvolution.trInv g * 1 * UpperTheory.Reformulated.B.ThetaInvolution.trInv h *
        UpperTheory.Reformulated.B.ThetaInvolution.Jgl R m := by rw [mul_one]; simp only [mul_assoc]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.thetaAut.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := UpperTheory.Reformulated.B.ThetaInvolution.theta, invFun := UpperTheory.Reformulated.B.ThetaInvolution.theta, left_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux8,
        right_inv := UpperTheory.Reformulated.B.ThetaInvolution.aux8, map_mul' := UpperTheory.Reformulated.B.ThetaInvolution.aux9 : GL (Fin m) R ≃* GL (Fin m) R }

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux11.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R],
      (if (1 : ℤˣ) = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) =
        (1 : MulAut (GL (Fin m) R)) := by
  intro m R _
  exact if_pos rfl

private theorem UpperTheory.Reformulated.B.ThetaInvolution.thetaAut_mul_self.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] :
    UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R * UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R = 1 :=
  MulEquiv.ext (fun g => UpperTheory.Reformulated.B.ThetaInvolution.aux8 g)

theorem UpperTheory.Reformulated.B.ThetaInvolution.aux12.{u_1} :
    ∀ (m : ℕ) (R : Type u_1) [inst : CommRing R] (s t : ℤˣ),
      (if s * t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) =
        (if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R) *
          if t = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R := by
  intro m R _ s t
  have hn : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hn]
  · simp [hn]
  · simp [hn, UpperTheory.Reformulated.B.ThetaInvolution.thetaAut_mul_self]

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.sgnAct.{u_1} :
    (m : ℕ) → (R : Type u_1) → [inst : CommRing R] → ℤˣ →* MulAut (GL (Fin m) R) :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦
      { toFun := fun (s : ℤˣ) ↦ if s = (1 : ℤˣ) then (1 : MulAut (GL (Fin m) R)) else UpperTheory.Reformulated.B.ThetaInvolution.thetaAut m R,
        map_one' := UpperTheory.Reformulated.B.ThetaInvolution.aux11 m R, map_mul' := UpperTheory.Reformulated.B.ThetaInvolution.aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.GG.{u_1} :
    ℕ → (R : Type u_1) → [CommRing R] → Type u_1 :=
    fun (m : ℕ) (R : Type u_1) [CommRing R] ↦ GL (Fin m) R ⋊[UpperTheory.Reformulated.B.ThetaInvolution.sgnAct m R] ℤˣ

@[reducible] noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.ofGL.{u_1} :
    {m : ℕ} → {R : Type u_1} → [inst : CommRing R] → GL (Fin m) R →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] ↦ SemidirectProduct.inl

noncomputable def UpperTheory.Reformulated.B.ThetaInvolution.conjBy.{u_1, u_3} :
    {m : ℕ} →
      {R : Type u_1} →
        [inst : CommRing R] →
          {G : Type u_3} → [inst_1 : Group G] → GL (Fin m) R → (G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R) → G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R :=
    fun {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G] (h : GL (Fin m) R) (r : G →* UpperTheory.Reformulated.B.ThetaInvolution.GG m R) ↦
      (MulEquiv.toMonoidHom
            ((MulAut.conj : UpperTheory.Reformulated.B.ThetaInvolution.GG m R → MulAut (UpperTheory.Reformulated.B.ThetaInvolution.GG m R))
              ((UpperTheory.Reformulated.B.ThetaInvolution.ofGL : GL (Fin m) R → UpperTheory.Reformulated.B.ThetaInvolution.GG m R) h))).comp
        r

theorem UpperTheory.Reformulated.B.ThetaInvolution.conjBy_conjBy :
    ∀ {C D : Type} [inst : CommRing C] [inst_1 : Group D] (h h' : GL (Fin (3 : ℕ)) C)
      (r : D →* UpperTheory.Reformulated.B.ThetaInvolution.GG (3 : ℕ) C),
      UpperTheory.Reformulated.B.ThetaInvolution.conjBy (h * h')⁻¹ (UpperTheory.Reformulated.B.ThetaInvolution.conjBy h r) = UpperTheory.Reformulated.B.ThetaInvolution.conjBy h'⁻¹ r := by
  intro C D _ _ h h' r
  ext1 x
  have e1 : (UpperTheory.Reformulated.B.ThetaInvolution.ofGL (h * h')⁻¹ : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) =
      (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h * UpperTheory.Reformulated.B.ThetaInvolution.ofGL h')⁻¹ := by rw [map_inv, map_mul]
  have e2 : (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h'⁻¹ : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) =
      (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h')⁻¹ := map_inv _ _
  change MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL (h * h')⁻¹)
      (MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h) (r x)) =
    MulAut.conj (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h'⁻¹) (r x)
  rw [e1, e2]
  generalize (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) = a
  generalize (UpperTheory.Reformulated.B.ThetaInvolution.ofGL h' : UpperTheory.Reformulated.B.ThetaInvolution.GG 3 C) = b
  generalize r x = y
  simp only [MulAut.conj_apply]
  group
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem entIn_sub_iff {C : Type} [CommRing C] (I : Ideal C) (X Y : Matrix (Fin 3) (Fin 3) C) :
    EntIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  · intro h a b
    exact Ideal.Quotient.eq.1 (congrFun (congrFun h a) b)

private theorem congOne_iff {C : Type} [CommRing C] (I : Ideal C) (h : GL (Fin 3) C) :
    CongOne I h ↔ GeneralLinearGroup.map (Ideal.Quotient.mk I) h = 1 := by
  unfold CongOne
  rw [entIn_sub_iff, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro e
    exact Units.ext e
  · intro e
    exact congrArg Units.val e

private theorem conjBy_app {C D : Type} [CommRing C] [Group D] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) (g : D) :
    conjBy h r g = GG.ofGL h * r g * (GG.ofGL h)⁻¹ := rfl

private theorem conjBy_comp {C D E : Type} [CommRing C] [Group D] [Group E] (h : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C))
    (f : E →* D) : (conjBy h r).comp f = conjBy h (r.comp f) := rfl

private theorem conjBy_conjBy {C D : Type} [CommRing C] [Group D] (h h' : GL (Fin 3) C)
    (r : D →* GG (m := 3) (R := C)) :
    conjBy (h * h')⁻¹ (conjBy h r) = conjBy h'⁻¹ r := by
  refine MonoidHom.ext fun g => ?_
  simp only [conjBy_app, map_inv, map_mul]
  group

private theorem map_conjBy {C D : Type} [CommRing C] [Group D] (I : Ideal C) (h : GL (Fin 3) C)
    (hh : CongOne I h) (r : D →* GG (m := 3) (R := C)) (g : D) :
    GG.map (Ideal.Quotient.mk I) (conjBy h r g) = GG.map (Ideal.Quotient.mk I) (r g) := by
  have e : GG.map (Ideal.Quotient.mk I) (GG.ofGL h) = 1 := by
    unfold GG.map
    rw [SemidirectProduct.map_inl, (congOne_iff I h).1 hh, map_one]
  simp only [conjBy, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv, e,
    one_mul, inv_one, mul_one]

theorem UpperTheory.V.UnitaryThreeInertia.cond_conj :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ] (F : Frame O G Γ ι) {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (h : GL (Fin 3) R), InHat h →
      (∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r)) ∧
        ∀ r : Γ →* GG (m := 3) (R := R), F.Cond r → F.Cond (conjBy h r) := by
  intro O _ _ G Γ ι _ _ F R _ _ _ h hh
  have hmul : ∀ h' : GL (Fin 3) R, InHat h' → InHat (h * h') := fun h' hh' => by
    refine (congOne_iff _ _).2 ?_
    rw [map_mul, (congOne_iff _ _).1 hh, (congOne_iff _ _).1 hh', mul_one]
  have hloc : ∀ v (r : F.D v →* GG (m := 3) (R := R)), F.LocAt v r → F.LocAt v (conjBy h r) := by
    intro v r ⟨ht, hd, hu⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e s hs => ?_⟩
    · obtain ⟨h', h1, h2, h3⟩ := ht e
      refine ⟨h * h', hmul h' h1, ?_, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
    · obtain ⟨h', h1, ⟨h2, h3⟩, h4⟩ := hd e
      refine ⟨h * h', hmul h' h1, ⟨?_, ?_⟩, ?_⟩
      · rw [conjBy_conjBy]; exact h2
      · rw [conjBy_conjBy]; exact h3
      · rw [conjBy_conjBy]; exact h4
    · rw [conjBy_app, hu e s hs, mul_one, mul_inv_cancel]
  refine ⟨hloc, fun r hr => ⟨⟨fun g => ?_, fun g => ?_⟩, fun v => ?_⟩⟩
  · have e := congrArg SemidirectProduct.right (map_conjBy _ h hh r g)
    rw [GG.map_right, GG.map_right] at e
    exact e.trans (hr.mult g)
  · have e := congrArg GG.mat (map_conjBy _ h hh r g)
    rw [GG.map_mat, GG.map_mat] at e
    rw [entIn_sub_iff, e, ← entIn_sub_iff]
    exact hr.red g
  · rw [conjBy_comp]
    exact hloc v _ (hr.loc v)
end
