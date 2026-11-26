module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MapDiagonalRepMatrixEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.CanonGr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.TorStep
open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.TorStep

theorem exists_procyc_lift {D H H' : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [Group H] [Finite H]
    [Group H'] (I : Subgroup D) (φ : D) (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (π : H →* H') (u' : D →* H') (hu' : IsLocallyConstant u') (hI : ∀ s ∈ I, u' s = 1) (y : H) (hy : π y = u' φ) :
    ∃ u : D →* H, IsLocallyConstant u ∧ (∀ s ∈ I, u s = 1) ∧ π.comp u = u' ∧ ∀ g, ∃ k : ℕ, u g = y ^ k := by
  have hn : 0 < orderOf y := orderOf_pos y
  obtain ⟨d, hd1, hd2, hd3⟩ := hd (orderOf y) hn
  haveI : NeZero (orderOf y) := ⟨hn.ne'⟩
  let e : Multiplicative (ZMod (orderOf y)) →* H :=
    { toFun := fun k => y ^ (Multiplicative.toAdd k).val
      map_one' := by simp
      map_mul' := fun a b => by rw [toAdd_mul, ZMod.val_add, pow_mod_orderOf, pow_add] }
  have he : e (Multiplicative.ofAdd 1) = y := by
    show y ^ (1 : ZMod (orderOf y)).val = y
    rw [ZMod.val_one_eq_one_mod, pow_mod_orderOf, pow_one]
  have hlc : IsLocallyConstant (e.comp d) := hd1.comp e
  refine ⟨e.comp d, hlc, fun s hs => by simp [hd2 s hs], ?_, fun g => ⟨_, rfl⟩⟩
  have h1 : I ⊔ Subgroup.zpowers φ ≤ (π.comp (e.comp d)).eqLocus u' := by
    refine sup_le (fun s hs => ?_) ?_
    · show π (e (d s)) = u' s
      rw [hd2 s hs, hI s hs, map_one, map_one]
    · rw [Subgroup.zpowers_le]
      show π (e (d φ)) = u' φ
      rw [hd3, he, hy]
  have h2 : IsClosed (((π.comp (e.comp d)).eqLocus u' : Subgroup D) : Set D) := by
    have := ((hlc.comp π).prodMk hu').isClopen_fiber
    have h3 := ((hlc.comp π).prodMk hu') {z | z.1 = z.2}ᶜ
    rw [← isOpen_compl_iff]
    exact h3
  have h4 := Subgroup.topologicalClosure_minimal _ h1 h2
  rw [hφ] at h4
  exact MonoidHom.ext fun g => h4 (Subgroup.mem_top g)

section

variable {R : Type} [CommRing R]

theorem inv_val_eq_pow [Finite R] (z : GL (Fin 3) R) :
    ∃ k : ℕ, ((z⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) = (z : Matrix (Fin 3) (Fin 3) R) ^ k := by
  refine ⟨orderOf z - 1, ?_⟩
  rw [← Units.val_pow_eq_pow_val]
  congr 1
  rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos z), pow_orderOf_eq_one]

theorem J_conj_apply (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (Jmat (R := R) 3 * Xᵀ * Jmat (R := R) 3) a b = X b.rev a.rev := by
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, Fin.rev]

theorem theta_apply (z : GL (Fin 3) R) (a b : Fin 3) :
    (theta z : Matrix (Fin 3) (Fin 3) R) a b = ((z⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) b.rev a.rev := by
  rw [theta_val, J_conj_apply]

theorem isDiag_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : X.IsDiag) (hY : Y.IsDiag) : (X * Y).IsDiag := by
  rw [← hX.diagonal_diag, ← hY.diagonal_diag, Matrix.diagonal_mul_diagonal]
  exact Matrix.isDiag_diagonal _

theorem isDiag_inv [Finite R] {z : GL (Fin 3) R} (hz : z.val.IsDiag) : (z⁻¹).val.IsDiag := by
  obtain ⟨k, hk⟩ := inv_val_eq_pow z
  rw [hk]
  clear hk
  induction k with
  | zero => rw [pow_zero]; exact Matrix.isDiag_one
  | succ k ih => rw [pow_succ]; exact isDiag_mul ih hz

theorem isDiag_GG_mul [Finite R] {z w : GG (m := 3) (R := R)} (hz : z.mat.IsDiag) (hw : w.mat.IsDiag) : (z * w).mat.IsDiag := by
  unfold GG.mat
  rw [SemidirectProduct.mul_left, Units.val_mul]
  refine isDiag_mul hz ?_
  rcases Int.units_eq_one_or z.right with h | h
  · rw [h, sgnAct_one]; exact hw
  · rw [h, sgnAct_neg_one]
    intro a b hab
    rw [theta_apply]
    exact isDiag_inv hw fun e => hab (Fin.rev_injective e).symm

theorem commute_tor {z : GG (m := 3) (R := R)} (hz : z.mat.IsDiag) (t : Rˣ) : Commute (GG.ofGL (tor (R := R) t)) z := by
  have h : sgnAct (m := 3) (R := R) z.right (tor (R := R) t) = tor (R := R) t := by
    rcases Int.units_eq_one_or z.right with h | h
    · rw [h, sgnAct_one]
    · rw [h, sgnAct_neg_one]
      apply Units.ext
      rw [theta_val, ← map_inv]
      change (Jmat (R := R) 3 * (Matrix.diagonal (fun i => (((t⁻¹) ^ wt1 i : Rˣ) : R)))ᵀ * Jmat (R := R) 3) =
        Matrix.diagonal (fun i => ((t ^ wt1 i : Rˣ) : R))
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_three, Jmat, wt1, Matrix.diagonal, Fin.rev]
  refine SemidirectProduct.ext ?_ (by simp)
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl, sgnAct_one, h]
  apply Units.ext
  have hz' : z.left.val = diagonal z.left.val.diag := (Matrix.IsDiag.diagonal_diag hz).symm
  rw [Units.val_mul, Units.val_mul, hz']
  change Matrix.diagonal (fun i => ((t ^ wt1 i : Rˣ) : R)) * diagonal z.left.val.diag =
    diagonal z.left.val.diag * Matrix.diagonal (fun i => ((t ^ wt1 i : Rˣ) : R))
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem map_tor {S : Type} [CommRing S] (f : R →+* S) (t : Rˣ) :
    GeneralLinearGroup.map f (tor (R := R) t) = tor (R := S) (Units.map f.toMonoidHom t) := by
  apply Units.ext
  ext a b
  show f ((tor (R := R) t).val a b) = _
  change f (Matrix.diagonal (fun i => ((t ^ wt1 i : Rˣ) : R)) a b) =
    Matrix.diagonal (fun i => (((Units.map f.toMonoidHom t) ^ wt1 i : Sˣ) : S)) a b
  rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [← map_zpow]; rfl
  · exact map_zero f

variable {O : Type} [CommRing O] [Algebra O R] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜]

theorem grMat_mul {X Y : Matrix (Fin 3) (Fin 3) R} (hX : GrMat 𝒜 X) (hY : GrMat 𝒜 Y) : GrMat 𝒜 (X * Y) := by
  intro a b
  rw [Matrix.mul_apply]
  refine Submodule.sum_mem _ fun c _ => ?_
  have : wt a b = wt a c + wt c b := by unfold wt; ring
  rw [this]
  exact SetLike.mul_mem_graded (hX a c) (hY c b)

theorem grMat_diagonal {d : Fin 3 → R} (hd : ∀ a, d a ∈ 𝒜 0) : GrMat 𝒜 (diagonal d) := by
  intro a b
  rw [Matrix.diagonal_apply]
  split_ifs with h
  · subst h
    have : wt a a = 0 := sub_self _
    rw [this]; exact hd a
  · exact zero_mem _

theorem grMat_one : GrMat 𝒜 (1 : Matrix (Fin 3) (Fin 3) R) :=
  grMat_diagonal 𝒜 (d := fun _ => 1) fun _ => SetLike.one_mem_graded 𝒜

theorem grMat_inv [Finite R] {z : GL (Fin 3) R} (hz : GrMat 𝒜 z.val) : GrMat 𝒜 (z⁻¹).val := by
  obtain ⟨k, hk⟩ := inv_val_eq_pow z
  rw [hk]
  clear hk
  induction k with
  | zero => rw [pow_zero]; exact grMat_one 𝒜
  | succ k ih => rw [pow_succ]; exact grMat_mul 𝒜 ih hz

theorem grMat_GG_mul [Finite R] {z w : GG (m := 3) (R := R)} (hz : GrMat 𝒜 z.mat) (hw : GrMat 𝒜 w.mat) :
    GrMat 𝒜 (z * w).mat := by
  unfold GG.mat
  rw [SemidirectProduct.mul_left, Units.val_mul]
  refine grMat_mul 𝒜 hz ?_
  rcases Int.units_eq_one_or z.right with h | h
  · rw [h, sgnAct_one]; exact hw
  · rw [h, sgnAct_neg_one]
    intro a b
    rw [theta_apply]
    have : wt a b = wt b.rev a.rev := by fin_cases a <;> fin_cases b <;> rfl
    rw [this]
    exact grMat_inv 𝒜 hw _ _

theorem grMat_tor (t : Oˣ) : GrMat 𝒜 (tor (R := R) (Units.map (algebraMap O R).toMonoidHom t)).val := by
  change GrMat 𝒜 (Matrix.diagonal (fun i => (((Units.map (algebraMap O R).toMonoidHom t) ^ wt1 i : Rˣ) : R)))
  refine grMat_diagonal 𝒜 fun a => ?_
  rw [← map_zpow]
  exact SetLike.algebraMap_mem_graded 𝒜 _

end

abbrev chr {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (A : Type) [CommRing A] [Algebra O A] : D →* Aˣ :=
  (Units.map (algebraMap O A).toMonoidHom).comp Ψ

theorem tor_chr_apply {O D : Type} [CommRing O] [Group D] (Ψ : D →* Oˣ) (A : Type) [CommRing A] [Algebra O A]
    (g : D) : (tor (R := A) (chr Ψ A g)).val = diagonal fun a => algebraMap O A (psi Ψ a g) := by
  change Matrix.diagonal (fun i => (((chr Ψ A g) ^ wt1 i : Aˣ) : A)) = _
  congr 1
  funext a
  show (((Units.map (algebraMap O A).toMonoidHom (Ψ g)) ^ wt1 a : Aˣ) : A) = _
  rw [← map_zpow]
  rfl

theorem isLocallyConstant_chr {O D : Type} [CommRing O] [IsLocalRing O] [Group D] [TopologicalSpace D] (Ψ : D →* Oˣ)
    (hΨ : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (Ψ g : O))
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] [Finite A] : IsLocallyConstant (chr Ψ A) := by
  obtain ⟨n, hn⟩ : IsNilpotent (maximalIdeal A) := by
    have := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] at this
  have hk : ∀ a ∈ maximalIdeal O ^ n, algebraMap O A a = 0 := by
    intro a ha
    have h1 : maximalIdeal O ^ n ≤ (maximalIdeal A ^ n).comap (algebraMap O A) := by
      refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) n) (Ideal.le_comap_pow _ n)
      exact map_nonunit (algebraMap O A) y hy
    have h2 := h1 ha
    rw [hn] at h2
    simpa using h2
  refine IsLocallyConstant.desc _ (Units.val) ?_ Units.val_injective
  exact (hΨ n).comp (Ideal.Quotient.lift _ _ hk)

theorem isLocallyConstant_GG {A D : Type} [CommRing A] [Group D] [TopologicalSpace D] (η : D →* ℤˣ)
    (hη : IsLocallyConstant η) (r : D →* GG (m := 3) (R := A)) (hr : HasMult η r) (h : IsLocallyConstant (mats r)) :
    IsLocallyConstant r := by
  refine IsLocallyConstant.desc _ (fun z : GG (m := 3) (R := A) => (z.mat, z.right)) ?_ ?_
  · have : (fun z : GG (m := 3) (R := A) => (z.mat, z.right)) ∘ r = fun g => (mats r g, η g) := by
      funext g
      exact Prod.ext rfl (hr g)
    rw [this]
    exact h.prodMk hη
  · intro z w e
    exact SemidirectProduct.ext (Units.ext (congrArg Prod.fst e)) (congrArg Prod.snd e)

def twist {A D : Type} [CommRing A] [Group D] (χ : D →* Aˣ) (u : D →* GG (m := 3) (R := A)) (hu : ∀ g, (u g).mat.IsDiag) :
    D →* GG (m := 3) (R := A) where
  toFun g := GG.ofGL (tor (R := A) (χ g)) * u g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul, map_mul]
    exact (commute_tor (hu g) (χ h)).mul_mul_mul_comm _ _

theorem exists_torus_lift {O D R R' : Type} [CommRing O] [IsLocalRing O] [Group D] [TopologicalSpace D]
    [IsTopologicalGroup D] [CommRing R] [Algebra O R] [IsCO O R] [Finite R] [CommRing R'] [Algebra O R'] [IsCO O R']
    [Finite R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') [IsLocalHom (p : R →+* R')]
    (I : Subgroup D) (φ : D) (hφ : (I ⊔ Subgroup.zpowers φ).topologicalClosure = ⊤)
    (hd : ∀ n : ℕ, 0 < n → ∃ d : D →* Multiplicative (ZMod n), IsLocallyConstant d ∧ (∀ s ∈ I, d s = 1) ∧
      d φ = Multiplicative.ofAdd 1)
    (Ψ : D →* Oˣ) (hΨ : ∀ n : ℕ, IsLocallyConstant fun g => Ideal.Quotient.mk (maximalIdeal O ^ n) (Ψ g : O))
    (t' : D →* GG (m := 3) (R := R')) (hlc : IsLocallyConstant t') (hdiag : ∀ g, (t' g).mat.IsDiag)
    (hI : ∀ s ∈ I, t' s = GG.ofGL (tor (R := R') (chr Ψ R' s)))
    (hgr : ∀ a, ∃ x ∈ 𝒜 0, p x = (t' φ).mat a a) :
    ∃ t : D →* GG (m := 3) (R := R), UnitaryThreeInertia.push p t = t' ∧ IsLocallyConstant t ∧ (∀ g, (t g).mat.IsDiag) ∧
      (∀ s ∈ I, t s = GG.ofGL (tor (R := R) (chr Ψ R s))) ∧ ∀ g, GrMat 𝒜 (t g).mat := by
  haveI : Finite (GG (m := 3) (R := R)) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  choose x hx0 hx using hgr
  have hdet : IsUnit (diagonal x).det := by
    have h1 : (diagonal x).map (p : R →+* R') = (t' φ).mat := by
      rw [Matrix.diagonal_map (map_zero _), ← (hdiag φ).diagonal_diag]
      congr 1
      funext a
      exact hx a
    apply IsUnit.of_map (p : R →+* R')
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h1]
    exact (Matrix.isUnit_iff_isUnit_det _).1 (t' φ).left.isUnit
  obtain ⟨X, hX⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hdet
  have hmt : ∀ g, GG.map (p : R →+* R') (GG.ofGL (tor (R := R) (chr Ψ R g))) = GG.ofGL (tor (R := R') (chr Ψ R' g)) := by
    intro g
    refine SemidirectProduct.ext ?_ rfl
    show GeneralLinearGroup.map _ (tor (R := R) (chr Ψ R g)) = tor (R := R') (chr Ψ R' g)
    rw [map_tor]
    congr 1
    exact Units.ext (p.commutes _)
  let y₀ : GG (m := 3) (R := R) := ⟨X, (t' φ).right⟩
  have hy₀ : GG.map (p : R →+* R') y₀ = t' φ := by
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    show X.val.map (p : R →+* R') = (t' φ).mat
    rw [hX, Matrix.diagonal_map (map_zero _), ← (hdiag φ).diagonal_diag]
    congr 1
    funext a
    exact hx a
  have htd : ∀ t : Rˣ, (GG.ofGL (tor (R := R) t)).mat.IsDiag := fun t => Matrix.isDiag_diagonal _
  have htg : ∀ g, GrMat 𝒜 (GG.ofGL (tor (R := R) (chr Ψ R g))).mat := fun g => grMat_tor 𝒜 (Ψ g)
  let y : GG (m := 3) (R := R) := GG.ofGL (tor (R := R) (chr Ψ R φ⁻¹)) * y₀
  have hyd : y.mat.IsDiag := isDiag_GG_mul (htd _) (by
    show X.val.IsDiag
    rw [hX]; exact Matrix.isDiag_diagonal _)
  have hyg : GrMat 𝒜 y.mat := grMat_GG_mul 𝒜 (htg _) (by
    show GrMat 𝒜 X.val
    rw [hX]; exact grMat_diagonal 𝒜 hx0)
  have hpow : ∀ k : ℕ, (y ^ k).mat.IsDiag ∧ GrMat 𝒜 (y ^ k).mat := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact ⟨Matrix.isDiag_one, grMat_one 𝒜⟩
    | succ k ih => rw [pow_succ]; exact ⟨isDiag_GG_mul ih.1 hyd, grMat_GG_mul 𝒜 ih.2 hyg⟩
  let u' : D →* GG (m := 3) (R := R') := twist (chr Ψ R')⁻¹ t' hdiag
  have hu' : ∀ g, u' g = (GG.ofGL (tor (R := R') (chr Ψ R' g)))⁻¹ * t' g := fun g => by
    rw [← map_inv, ← map_inv]; rfl
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := exists_procyc_lift I φ hφ hd (GG.map (p : R →+* R')) u'
    (((isLocallyConstant_chr Ψ hΨ R').prodMk hlc).comp fun z => GG.ofGL (tor (R := R') z.1⁻¹) * z.2)
    (fun s hs => by rw [hu', hI s hs, inv_mul_cancel]) y
    (by rw [hu', map_mul, hmt, hy₀, map_inv, map_inv, map_inv])
  have hud : ∀ g, (u g).mat.IsDiag := fun g => by
    obtain ⟨k, hk⟩ := hu4 g
    rw [hk]; exact (hpow k).1
  refine ⟨twist (chr Ψ R) u hud, MonoidHom.ext fun g => ?_,
    ((isLocallyConstant_chr Ψ hΨ R).prodMk hu1).comp fun z => GG.ofGL (tor (R := R) z.1) * z.2,
    fun g => isDiag_GG_mul (htd _) (hud g), fun s hs => ?_, fun g => grMat_GG_mul 𝒜 (htg g) ?_⟩
  · show GG.map _ (GG.ofGL (tor (R := R) (chr Ψ R g)) * u g) = t' g
    have : GG.map (p : R →+* R') (u g) = u' g := DFunLike.congr_fun hu3 g
    rw [map_mul, hmt, this, hu', mul_inv_cancel_left]
  · show GG.ofGL (tor (R := R) (chr Ψ R s)) * u s = _
    rw [hu2 s hs, mul_one]
  · obtain ⟨k, hk⟩ := hu4 g
    rw [hk]; exact (hpow k).2

end UpperTheory.V.UnitaryThreeInertia.TorStep
end

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

section

open UpperTheory.V.UnitaryThreeInertia.TorStep

variable {O A D : Type} [CommRing O] [CommRing A] [IsLocalRing A] [Algebra O A] [Group D]

private theorem psi_diff (Ψ : D →* Oˣ) (x : D) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (a b : Fin 3) (hab : a ≠ b) :
    IsUnit (psi Ψ a x - psi Ψ b x) := by
  have h0 : psi Ψ 0 x = (Ψ x : O) := by simp [psi, wt1]
  have h1 : psi Ψ 1 x = 1 := by simp [psi, wt1]
  have h2 : psi Ψ 2 x = ((Ψ x)⁻¹ : Oˣ) := by simp [psi, wt1]
  have hi : (Ψ x : O) * ((Ψ x)⁻¹ : Oˣ) = 1 := Units.mul_inv _
  have e01 : IsUnit (psi Ψ 0 x - psi Ψ 1 x) := by
    rw [h0, h1]
    exact isUnit_of_mul_isUnit_left (y := (Ψ x : O) + 1) (by convert hx using 1; ring)
  have e12 : IsUnit (psi Ψ 1 x - psi Ψ 2 x) := by
    rw [h0, h1] at e01
    rw [h1, h2]
    convert e01.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -hi
  have e02 : IsUnit (psi Ψ 0 x - psi Ψ 2 x) := by
    rw [h0, h2]
    convert hx.mul ((Ψ x)⁻¹).isUnit using 1
    linear_combination -(Ψ x : O) * hi
  have neg : ∀ {u w : O}, IsUnit (u - w) → IsUnit (w - u) := fun h => by rw [← neg_sub]; exact h.neg
  fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | assumption | (apply neg; assumption)

private theorem unit_of_res {y : A} {u : O} (hu : IsUnit u) (h : residue A y = residue A (algebraMap O A u)) :
    IsUnit y := by
  rw [← residue_ne_zero_iff_isUnit, h, residue_ne_zero_iff_isUnit]
  exact hu.map _

private theorem res_left [IsLocalRing O] {η : D →* ℤˣ} {Ψ : D →* Oˣ} {r : D →* GG (m := 3) (R := A)} (hr : Red η Ψ r) (g : D) :
    GeneralLinearGroup.map (residue A) (r g).left = GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)) := by
  apply Units.ext
  ext a b
  have h := (residue_eq_zero_iff _).2 (hr.red g a b)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
  have h2 : GeneralLinearGroup.map (algebraMap O A) (tor O (Ψ g)) = tor A (chr Ψ A g) := map_tor _ _
  rw [← h2]
  exact h

private theorem res_conj {h : GL (Fin 3) A} (hh : InHat h) (r : D →* GG (m := 3) (R := A)) (g : D) :
    GeneralLinearGroup.map (residue A) (conjBy h⁻¹ r g).left = GeneralLinearGroup.map (residue A) (r g).left := by
  have h1 : GG.map (residue A) (GG.ofGL h) = 1 := by
    refine SemidirectProduct.ext (Units.ext ?_) rfl
    ext a b
    have h := (residue_eq_zero_iff _).2 (hh a b)
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h
    refine h.trans ?_
    show _ = (1 : Matrix (Fin 3) (Fin 3) _) a b
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : GG.map (residue A) (conjBy h⁻¹ r g) = GG.map (residue A) (r g) := by
    show GG.map (residue A) (GG.ofGL h⁻¹ * r g * (GG.ofGL h⁻¹)⁻¹) = _
    simp only [map_mul, map_inv, h1, inv_one, one_mul, mul_one]
  exact congrArg SemidirectProduct.left h2

private theorem diag_all [Finite A] {η : D →* ℤˣ} {Ψ : D →* Oˣ} (t : D →* GG (m := 3) (R := A)) (hm : HasMult η t)
    (hres : ∀ g, GeneralLinearGroup.map (residue A) (t g).left =
      GeneralLinearGroup.map (residue A) (tor A (chr Ψ A g)))
    (hd : ∀ g, η g = 1 → (t g).mat.IsDiag) (x : D) (hηx : η x = 1) (hx : IsUnit ((Ψ x : O) ^ 2 - 1)) (g : D) :
    (t g).mat.IsDiag := by
  rcases Int.units_eq_one_or (η g) with hg | hg
  · exact hd g hg
  have hη2 : η (g * x * g⁻¹) = 1 := by rw [map_mul, map_mul, hηx, mul_one, map_inv, mul_inv_cancel]
  have hΨ2 : chr Ψ A (g * x * g⁻¹) = chr Ψ A x := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  have e : t (g * x * g⁻¹) * t g = t g * t x := by rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  have e1 : (t (g * x * g⁻¹)).mat * (t g).mat = (t g).mat * (theta (t x).left).val := by
    have := congrArg (fun z : GG (m := 3) (R := A) => z.left.val) e
    simpa only [GG.mat, SemidirectProduct.mul_left, hm _, hη2, hg, sgnAct_one, sgnAct_neg_one, Units.val_mul] using this
  have d1 := hd _ hη2
  have d2 : (theta (t x).left).val.IsDiag := by
    intro a b hab
    rw [theta_apply]
    exact isDiag_inv (hd x hηx) fun e => hab (Fin.rev_injective e).symm
  have r1 : ∀ a, residue A ((t (g * x * g⁻¹)).mat a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) (hres (g * x * g⁻¹))
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [hΨ2, tor_chr_apply, Matrix.diagonal_apply_eq]
  have r2 : ∀ a, residue A ((theta (t x).left).val a a) = residue A (algebraMap O A (psi Ψ a x)) := by
    intro a
    have h3 : GeneralLinearGroup.map (residue A) (theta (t x).left) =
        GeneralLinearGroup.map (residue A) (tor A (chr Ψ A x)) := by
      rw [map_theta, hres, ← map_theta, theta_tor]
    have := congrArg (fun z : GL (Fin 3) _ => z.val a a) h3
    refine this.trans ?_
    show residue A ((tor A _).val a a) = _
    rw [tor_chr_apply, Matrix.diagonal_apply_eq]
  intro a b hab
  have hu : IsUnit ((t (g * x * g⁻¹)).mat a a - (theta (t x).left).val b b) :=
    unit_of_res (psi_diff Ψ x hx a b hab) (by rw [map_sub, map_sub, map_sub, r1, r2])
  have e2 := congrFun (congrFun e1 a) b
  rw [← d1.diagonal_diag, ← d2.diagonal_diag, Matrix.diagonal_mul, Matrix.mul_diagonal] at e2
  apply hu.mul_left_cancel
  simp only [Matrix.diag_apply] at e2
  linear_combination e2

end

theorem UpperTheory.V.UnitaryThreeInertia.exists_lift_d :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → ∀ {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R'] (𝒜 : ℤ → Submodule O R) [GradedAlgebra 𝒜] (p : R →ₐ[O] R') (j : ℤ), Function.Surjective p → SmallExt O 𝒜 (RingHom.ker p) j →
    ∀ (v : ι), v ∈ F.Sb → ∀ (r' : F.D v →* GG (m := 3) (R := R')), Red (F.ηv v) (F.Ψv v) r' → F.LocAt v r' → IsLocallyConstant (mats r') →
      (∀ g, ∃ X, GrMat 𝒜 X ∧ X.map p = (r' g).mat) →
      ∃ r : F.D v →* GG (m := 3) (R := R), push p r = r' ∧ F.LocAt v r ∧ IsLocallyConstant (mats r) ∧ ∀ g, GrMat 𝒜 (r g).mat := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF _ R R' _ _ _ _ _ _ 𝒜 _ p j hp hS v hv r' hred hloc hlc hgr
  haveI : Finite R := hS.fin
  haveI : Finite R' := Finite.of_surjective p hp
  haveI : IsLocalHom (p : R →+* R') := IsLocalHom.of_surjective _ hp
  have hvT : v ∈ F.Tb := Set.mem_insert_of_mem _ hv
  have hcont : Continuous (F.loc v) := hF.π_cont.comp continuous_subtype_val
  obtain ⟨x, hηx, hx⟩ := hF.x v hvT
  obtain ⟨φ, hφ, hd⟩ := hF.frob v
  obtain ⟨X, hXg, hX⟩ := hgr x
  have hXp : ∀ a b, (p : R →+* R') (X a b) = (r' x).mat a b := fun a b => congrFun (congrFun hX a) b
  have hrx : ∀ a b, residue R' ((r' x).mat a b) =
      residue R' (diagonal (fun a => algebraMap O R' (psi (F.Ψv v) a x)) a b) := fun a b => by
    rw [← TorStep.tor_chr_apply]
    exact congrArg (fun z : GL (Fin 3) _ => z.val a b) (res_left hred x)
  have hXu : ∀ a b, a ≠ b → IsUnit (X a a - X b b) := fun a b hab => by
    apply IsUnit.of_map (p : R →+* R')
    refine unit_of_res (psi_diff _ x hx a b hab) ?_
    rw [map_sub, map_sub, map_sub, map_sub, hXp, hXp, hrx, hrx, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]
  have hXm : ∀ a b, a ≠ b → X a b ∈ maximalIdeal R := fun a b hab hu => by
    have h1 := hu.map (p : R →+* R')
    rw [hXp, ← residue_ne_zero_iff_isUnit, hrx, Matrix.diagonal_apply_ne _ hab, map_zero] at h1
    exact h1 rfl
  obtain ⟨h, hh⟩ := exists_canon X hXu hXm
  obtain ⟨hg1, hg2⟩ := canon_graded 𝒜 X h hXu hXg hh
  have hh' := canon_map.1 (p : R →+* R') X h hh
  rw [show X.map (p : R →+* R') = (r' x).mat from hX] at hh'
  set h' := GeneralLinearGroup.map (p : R →+* R') h with hh'def
  have hD : DiagIn (F.ηv v) (F.Ψv v) (F.Iv v) r' h' :=
    (cond_iff_canon _ _ _ r' x h' hred hηx hx hh').2.1 (hloc.2.1 hv)
  have hconj : ∀ {A : Type} [CommRing A] (k : GL (Fin 3) A) (r : F.D v →* GG (m := 3) (R := A)) (g : F.D v),
      conjBy k r g = GG.ofGL k * r g * GG.ofGL k⁻¹ := fun k r g => by rw [map_inv]; rfl
  have hmap : ∀ k : GL (Fin 3) R, GG.map (p : R →+* R') (GG.ofGL k) =
      GG.ofGL (GeneralLinearGroup.map (p : R →+* R') k) := fun k => rfl
  have hm : HasMult (F.ηv v) (conjBy h'⁻¹ r') := fun g => by
    rw [hconj]
    simp [hred.mult g]
  have hdiag : ∀ g, (conjBy h'⁻¹ r' g).mat.IsDiag := by
    refine diag_all (Ψ := F.Ψv v) _ hm (fun g => (res_conj hh'.hat r' g).trans (res_left hred g)) ?_ x hηx hx
    intro g hg a b hab
    rcases lt_trichotomy (wt a b) 0 with h0 | h0 | h0
    · exact hD.tri g hg a b h0
    · exact absurd (Fin.ext (by unfold wt wt1 at h0; omega)) hab
    · exact hD.low g hg a b h0
  have hlc' : IsLocallyConstant r' :=
    TorStep.isLocallyConstant_GG (F.ηv v) (hF.η_cont.comp_continuous hcont) r' hred.mult hlc
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5⟩ := TorStep.exists_torus_lift 𝒜 p (F.Iv v) φ hφ hd (F.Ψv v)
    (fun n => (hF.Ψ_cont n).comp_continuous hcont) (conjBy h'⁻¹ r')
    (hlc'.comp (MulAut.conj (GG.ofGL h'⁻¹))) hdiag
    (fun s hs => by
      refine SemidirectProduct.ext (Units.ext ?_) ((hm s).trans (hF.η_I v hvT s hs))
      show (conjBy h'⁻¹ r' s).mat = (tor R' _).val
      rw [TorStep.tor_chr_apply, ← (hdiag s).diagonal_diag]
      congr 1
      funext a
      exact hD.ine s hs (hF.η_I v hvT s hs) a)
    (fun a => by
      obtain ⟨W, hW1, hW2⟩ := hgr φ
      have hWu : IsUnit W := by
        rw [Matrix.isUnit_iff_isUnit_det]
        apply IsUnit.of_map (p : R →+* R')
        rw [RingHom.map_det, RingHom.mapMatrix_apply, show W.map (p : R →+* R') = (r' φ).mat from hW2]
        exact (Matrix.isUnit_iff_isUnit_det _).1 (r' φ).left.isUnit
      obtain ⟨W, rfl⟩ := hWu
      let w : GG (m := 3) (R := R) := ⟨W, (r' φ).right⟩
      have hw : GG.map (p : R →+* R') w = r' φ := SemidirectProduct.ext (Units.ext hW2) rfl
      have h1 : GrMat 𝒜 (GG.ofGL h⁻¹ * w * GG.ofGL h).mat :=
        TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg2 hW1) hg1
      have h2 : GG.map (p : R →+* R') (GG.ofGL h⁻¹ * w * GG.ofGL h) = conjBy h'⁻¹ r' φ := by
        rw [hconj, map_mul, map_mul, hw, hmap, hmap, map_inv, inv_inv]
      refine ⟨(GG.ofGL h⁻¹ * w * GG.ofGL h).mat a a, ?_, ?_⟩
      · have := h1 a a
        rwa [show wt a a = 0 from sub_self _] at this
      · rw [← h2]; rfl)
  have hback : conjBy h⁻¹ (conjBy h t) = t := MonoidHom.ext fun g => by
    rw [hconj, hconj, inv_inv, map_inv]; group
  refine ⟨conjBy h t, MonoidHom.ext fun g => ?_, ⟨fun e => absurd (e ▸ hv) hF.vl_notMem, fun _ => ⟨h, hh.hat, ?_⟩,
    fun e => absurd hvT e⟩, (ht2.comp (MulAut.conj (GG.ofGL h))).comp GG.mat, fun g => ?_⟩
  · show GG.map _ (conjBy h t g) = r' g
    have : GG.map (p : R →+* R') (t g) = conjBy h'⁻¹ r' g := DFunLike.congr_fun ht1 g
    rw [hconj, map_mul, map_mul, this, hconj, hmap, hmap]
    simp only [map_inv, ← hh'def]
    group
  · refine ⟨⟨fun g _ a b h0 => ?_, fun s hs _ a => ?_⟩, fun g _ a b h0 => ?_⟩
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
    · rw [hback, ht4 s hs]
      show (tor R _).val a a = _
      rw [TorStep.tor_chr_apply, Matrix.diagonal_apply_eq]
    · rw [hback]
      exact ht3 g fun e => by subst e; simp [wt] at h0
  · rw [hconj]
    exact TorStep.grMat_GG_mul 𝒜 (TorStep.grMat_GG_mul 𝒜 hg1 (ht5 g)) hg2
