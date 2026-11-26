module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdECut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCloseAt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxModes
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxCong
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxAt
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZhatOMMono
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

section Gen

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

theorem zLoc_mono (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (σ : Fin (r + 1) → Fin (r + 1))
    (ν : Fin (r + 1) → E) :
    zLoc ι cj Dd (mono σ ν) = mono σ (fun a => Dd (σ a) * cj (Dd a) * ι (ν a)) := by
  ext a b
  simp only [zLoc, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem zhatOM_mono (σ : Fin (r + 1) → Fin (r + 1)) (ν : Fin (r + 1) → E) :
    ZhatOM (mono σ ν) = mono σ (fun a => (-1) ^ (r - (σ a).val) * ν a) := by
  ext a b
  simp only [ZhatOM, mono, Matrix.of_apply]
  split_ifs with h
  · subst h; rfl
  · simp

theorem linG_mono {F : Type*} [Field F] [Algebra F K] (e : K ≃ₐ[F] F × F) (q : F) {σ : Fin (r + 1) → Fin (r + 1)}
    (hσ : ∀ a, σ (σ a) = a) (ν : Fin (r + 1) → K) :
    linG e q (mono σ ν) = mono σ (fun a => e.symm ((e (ν a)).1 / q, -((e (ν (σ a))).2 / q))) := by
  ext a b
  simp only [linG, mono, Matrix.of_apply]
  by_cases h : b = σ a
  · subst h
    rw [if_pos rfl, if_pos (hσ a).symm, if_pos rfl]
  · have h' : ¬ a = σ b := fun h' => h (by rw [h', hσ])
    rw [if_neg h, if_neg h', if_neg h]
    simp

theorem fix_single {K : Type*} [CommRing K] {l ρ : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) :
    l * Matrix.single (Fin.last r) (Fin.last r) κ * ρ = Matrix.single (Fin.last r) (Fin.last r) κ := by
  ext x y
  rw [mul_single_mul]
  have h1 : l x (Fin.last r) = if x = Fin.last r then 1 else 0 := by
    by_cases hx : x = Fin.last r
    · subst hx; rw [if_pos rfl]; exact (hl _ _).2 rfl
    · rw [if_neg hx]; exact (hl _ _).1 (lt_of_le_of_ne (Fin.le_last x) hx)
  have h2 : ρ (Fin.last r) y = if y = Fin.last r then 1 else 0 := by
    by_cases hy : y = Fin.last r
    · subst hy; rw [if_pos rfl]; exact (hρ _ _).2 rfl
    · rw [if_neg hy]; exact (hρ _ _).1 (lt_of_le_of_ne (Fin.le_last y) hy)
  rw [h1, h2, Matrix.single_apply]
  by_cases hx : x = Fin.last r <;> by_cases hy : y = Fin.last r
  · subst hx; subst hy; simp
  · simp [hy, Ne.symm hy]
  · simp [hx, Ne.symm hx]
  · simp [hx, Ne.symm hx]

theorem fix_of_fix {K : Type*} [CommRing K] {l ρ N : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hl : IsLoUni l)
    (hρ : IsUpUni ρ) (κ : K) (h : l * (N - Matrix.single (Fin.last r) (Fin.last r) κ) * ρ =
      N - Matrix.single (Fin.last r) (Fin.last r) κ) : l * N * ρ = N := by
  rw [Matrix.mul_sub, Matrix.sub_mul, fix_single hl hρ] at h
  exact sub_left_injective h

end Gen

section Rec

open Formalism.L2.SG.CntLocal

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (u u' : D.what₂.Word)

theorem zzp_mono {p : PlF D} (hA : Agree δ M p) {σ : Fin (D.R.rS + 1) → Fin (D.R.rS + 1)} (hσ : ∀ a, σ (σ a) = a)
    (ν : Fin (D.R.rS + 1) → D.host.E) (hν : ∀ a, ν a ≠ 0) :
    ∃ ν' : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν' a)) ∧ ∃ κ : (D.s.atP p).Ep,
      ZZP (M := M) δ u u' p (mono σ ν) = mono σ ν' - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
  set cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep := ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep)
  have hu : ∀ a, IsUnit (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a)) := fun a =>
    ((frFac_unit δ M hA (σ a)).mul ((frFac_unit δ M hA a).map cj)).mul ((isUnit_iff_ne_zero.2 (hν a)).map _)
  cases h : (M p).split with
  | none =>
    refine ⟨fun a => frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a), hu, 0, ?_⟩
    rw [zzp_none δ M u u' h, zLoc_mono, Matrix.single_zero, sub_zero]
  | some g =>
    refine ⟨fun a => g.e.symm ((g.e (frFac δ p (σ a) * cj (frFac δ p a) * (D.s.atP p).ιE (ν a))).1 / (g.q : (D.s.atP p).Fp),
      -((g.e (frFac δ p (σ (σ a)) * cj (frFac δ p (σ a)) * (D.s.atP p).ιE (ν (σ a)))).2 / (g.q : (D.s.atP p).Fp))),
      fun a => ?_, g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp)), ?_⟩
    · have hq := q_ne M g
      have h1 := (Prod.isUnit_iff.1 ((hu a).map g.e)).1
      have h2 := (Prod.isUnit_iff.1 ((hu (σ a)).map g.e)).2
      refine IsUnit.map g.e.symm (Prod.isUnit_iff.2 ⟨?_, ?_⟩)
      · exact isUnit_iff_ne_zero.2 (div_ne_zero h1.ne_zero hq)
      · exact isUnit_iff_ne_zero.2 (neg_ne_zero.2 (div_ne_zero h2.ne_zero hq))
    · rw [zzp_some δ M u u' h, zLoc_mono, linG_mono _ _ hσ]

end Rec

end Formalism.L2.SG.Pf.ProdEApprox
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EntInSandwich
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxClose
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Proj

variable {A : Type*} [CommRing A] {n : ℕ}

theorem entIn_transpose {J : AddSubgroup A} {X : Matrix (Fin n) (Fin n) A} (h : EntIn J X) : EntIn J X.transpose :=
  fun i j => h j i

theorem entIn_smul {J : AddSubgroup A} (e : A) (hJ : ∀ x ∈ J, e * x ∈ J) {X : Matrix (Fin n) (Fin n) A}
    (h : EntIn J X) : EntIn J (e • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact hJ _ (h i j)

theorem proj_inv (f : Fin n → ℕ) (hf : ∀ i, f i < n) {J : AddSubgroup A} (hJ : ∀ x ∈ J, ∀ y ∈ J, x * y ∈ J)
    (e : A) (he : e * e = e) (x : GL (Fin n) A)
    (hlow : ∀ i j, f i ≤ f j → ((x : Matrix (Fin n) (Fin n) A) - 1) i j = 0)
    (hx : EntIn J (e • ((x : Matrix (Fin n) (Fin n) A) - 1))) :
    EntIn J (e • (((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1)) := by
  set X := (x : Matrix (Fin n) (Fin n) A) - 1 with hXd
  set Y := ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 with hYd
  have hx1 : (x : Matrix (Fin n) (Fin n) A) = 1 + X := by rw [hXd]; abel
  have hy1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 + Y := by rw [hYd]; abel
  have hXY : X + Y + X * Y = 0 := by
    have h1 : (x : Matrix (Fin n) (Fin n) A) * ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + X) * (1 + Y) = (1 : Matrix (Fin n) (Fin n) A) + (X + Y + X * Y) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hYX : Y + X + Y * X = 0 := by
    have h1 : ((x⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * (x : Matrix (Fin n) (Fin n) A) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    rw [hx1, hy1] at h1
    have h2 : (1 + Y) * (1 + X) = (1 : Matrix (Fin n) (Fin n) A) + (Y + X + Y * X) := by
      simp only [add_mul, mul_add, one_mul, mul_one]; abel
    rw [h2] at h1
    simpa using h1
  have hv : (1 + e • X) * (1 + e • Y) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • Y + (e • X + e • (X * Y)) = e • (X + Y + X * Y) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hXY, smul_zero, add_zero]
  have hv' : (1 + e • Y) * (1 + e • X) = 1 := by
    rw [add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]
    have : e • X + (e • Y + e • (Y * X)) = e • (Y + X + Y * X) := by rw [smul_add, smul_add]; abel
    rw [add_assoc, this, hYX, smul_zero, add_zero]
  let y : GL (Fin n) A := ⟨1 + e • X, 1 + e • Y, hv, hv'⟩
  have hyv : (y : Matrix (Fin n) (Fin n) A) - 1 = e • X := by simp [y]
  have hyi : ((y⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) - 1 = e • Y := by
    show (1 + e • Y) - 1 = e • Y
    simp
  have key := inv_sub_one f hf hJ y (fun i j h => by
      rw [hyv, Matrix.smul_apply, hlow i j h, smul_zero]) (by rw [hyv]; exact hx)
  rw [hyi] at key
  exact key.1

end Proj

section Close

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L c') :
    x ∈ latS L c := by
  rw [h] at hx; exact latS_mono ht hx

theorem entIn_latS_of_eq {c c' t : L.Fp} (h : c' = c * t) (ht : t ∈ 𝒪[L.Fp]) {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L c') X) : EntIn (latS L c) X := fun i j => latS_of_eq h ht (hX i j)

end Close

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Close2

open Formalism.MainNotions.S.Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} {L : LocAt F E sig p} {n : ℕ}

theorem entIn_sandwich {P Q X : Matrix (Fin n) (Fin n) L.Ep} {sP sQ c : L.Fp}
    (hP : ∀ i j, algebraMap L.Fp L.Ep sP * P i j ∈ L.O) (hQ : ∀ i j, algebraMap L.Fp L.Ep sQ * Q i j ∈ L.O)
    (hX : EntIn (latS L (sP * (sQ * c))) X) : EntIn (latS L c) (P * X * Q) :=
  entIn_mul_right hQ (entIn_mul_left hP hX)

theorem smul_sandwich (e : L.Ep) (P X Q : Matrix (Fin n) (Fin n) L.Ep) : P * (e • X) * Q = e • (P * X * Q) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem close (ex ey : L.Ep) (hex : ex ∈ L.O) (hey : ey ∈ L.O) (hxx : ex * ex = ex) (hyy : ey * ey = ey)
    (hsum : ex + ey = 1) (hxy : ex * ey = 0)
    (N Ni Δ Δi Γ Γi : Matrix (Fin n) (Fin n) L.Ep) (hN : N * Ni = 1) (hN' : Ni * N = 1) (hΔ : Δ * Δi = 1)
    (hΓ : Γ * Γi = 1) (hΓ' : Γi * Γ = 1) (h1 h2 : GL (Fin n) L.Ep)
    (hh : (h1 : Matrix (Fin n) (Fin n) L.Ep) * N * (h2 : Matrix (Fin n) (Fin n) L.Ep) = N) (c : L.Fp) (hc0 : c ≠ 0) (hc : c ∈ 𝒪[L.Fp]) :
    ∃ c' : L.Fp, c' ≠ 0 ∧ c' ∈ 𝒪[L.Fp] ∧ ∀ (l ρ : GL (Fin n) L.Ep) (G : Matrix (Fin n) (Fin n) L.Ep),
      (∀ i j, i ≤ j → (((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) i j = 0) →
      (∀ i j, j ≤ i → (((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) i j = 0) →
      (l : Matrix (Fin n) (Fin n) L.Ep) * N * (ρ : Matrix (Fin n) (Fin n) L.Ep) = N →
      ex • (l : Matrix (Fin n) (Fin n) L.Ep) = ex • (Δ * G * Δi) →
      ey • (ρ : Matrix (Fin n) (Fin n) L.Ep) = ey • (Γi * G.transpose * Γ) →
      EntIn (latS L c') (G - (ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) +
        ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi).transpose)) →
      EntIn (latS L c) (((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) ∧
        EntIn (latS L c) (((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) - 1) := by
  obtain ⟨sN, hsN0, hsNO, hsN⟩ := bounded_mat (L := L) N
  obtain ⟨sNi, hsNi0, hsNiO, hsNi⟩ := bounded_mat (L := L) Ni
  obtain ⟨sA, hsA0, hsAO, hsA⟩ := bounded_mat (L := L) (((h1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) * Δ)
  obtain ⟨sB, hsB0, hsBO, hsB⟩ := bounded_mat (L := L) Δi
  obtain ⟨sC, hsC0, hsCO, hsC⟩ := bounded_mat (L := L) Γi
  obtain ⟨sD, hsD0, hsDO, hsD⟩ := bounded_mat (L := L) (Γ * ((h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep))
  set c1 := sNi * (sN * c) with hc1
  have hc1O : c1 ∈ 𝒪[L.Fp] := Subring.mul_mem _ hsNiO (Subring.mul_mem _ hsNO hc)
  have hc10 : c1 ≠ 0 := mul_ne_zero hsNi0 (mul_ne_zero hsN0 hc0)
  refine ⟨sA * (sB * (sC * (sD * c1))), mul_ne_zero hsA0 (mul_ne_zero hsB0 (mul_ne_zero hsC0 (mul_ne_zero hsD0 hc10))),
    Subring.mul_mem _ hsAO (Subring.mul_mem _ hsBO (Subring.mul_mem _ hsCO (Subring.mul_mem _ hsDO hc1O))), ?_⟩
  intro l ρ G hk1 hk2 hlN hlx hρy hG
  set h1i := ((h1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hh1i
  set h2i := ((h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hh2i
  set τ := ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) + ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi).transpose
    with hτ
  set D := G - τ with hD
  have h11 : h1i * h1 = 1 := by rw [hh1i, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h22 : (h2 : Matrix (Fin n) (Fin n) L.Ep) * h2i = 1 := by rw [hh2i, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hk1v : ((h1⁻¹ * l : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) = h1i * l := Units.val_mul _ _
  have hk2v : ((ρ * h2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) = ρ * h2i := Units.val_mul _ _
  have hτx : ex • τ = ex • (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) := by
    rw [hτ, smul_add, smul_smul, smul_smul, hxx, hxy, zero_smul, add_zero]
  have hτy : ey • τ.transpose = ey • (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi) := by
    rw [hτ, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_transpose, smul_add,
      smul_smul, smul_smul, hyy, mul_comm ey ex, hxy, zero_smul, zero_add]

  have E1 : ex • (h1i * l - 1) = (h1i * Δ) * (ex • D) * Δi := by
    have a1 : (h1i * Δ) * (ex • D) * Δi = h1i * (Δ * (ex • G) * Δi) - h1i * (Δ * (ex • τ) * Δi) := by
      rw [hD, smul_sub, Matrix.mul_sub, Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    have a2 : Δ * (ex • G) * Δi = ex • (l : Matrix (Fin n) (Fin n) L.Ep) := by rw [smul_sandwich, hlx]
    have a3 : Δ * (ex • τ) * Δi = ex • (h1 : Matrix (Fin n) (Fin n) L.Ep) := by
      rw [hτx, smul_sandwich]
      congr 1
      rw [show Δ * (Δi * (h1 : Matrix (Fin n) (Fin n) L.Ep) * Δ) * Δi = (Δ * Δi) * h1 * (Δ * Δi) by
        simp only [Matrix.mul_assoc], hΔ, Matrix.one_mul, Matrix.mul_one]
    rw [a1, a2, a3, Matrix.mul_smul, Matrix.mul_smul, h11, smul_sub]
  have E2 : ey • (ρ * h2i - 1) = Γi * (ey • D).transpose * (Γ * h2i) := by
    have b1 : Γi * (ey • D).transpose * (Γ * h2i) =
        (Γi * (ey • G.transpose) * Γ) * h2i - (Γi * (ey • τ.transpose) * Γ) * h2i := by
      rw [hD, smul_sub, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.mul_sub,
        Matrix.sub_mul]
      simp only [Matrix.mul_assoc]
    have b2 : Γi * (ey • G.transpose) * Γ = ey • (ρ : Matrix (Fin n) (Fin n) L.Ep) := by rw [smul_sandwich, hρy]
    have b3 : Γi * (ey • τ.transpose) * Γ = ey • (h2 : Matrix (Fin n) (Fin n) L.Ep) := by
      rw [hτy, smul_sandwich]
      congr 1
      rw [show Γi * (Γ * (h2 : Matrix (Fin n) (Fin n) L.Ep) * Γi) * Γ = (Γi * Γ) * h2 * (Γi * Γ) by
        simp only [Matrix.mul_assoc], hΓ', Matrix.one_mul, Matrix.mul_one]
    rw [b1, b2, b3, Matrix.smul_mul, Matrix.smul_mul, h22, smul_sub]

  have hexJ : ∀ {c'' : L.Fp}, ∀ x ∈ latS L c'', ex * x ∈ latS L c'' := fun x hx => O_mul_latS hex hx
  have heyJ : ∀ {c'' : L.Fp}, ∀ x ∈ latS L c'', ey * x ∈ latS L c'' := fun x hx => O_mul_latS hey hx
  have hD1 : EntIn (latS L (sA * (sB * c1))) (ex • D) :=
    entIn_smul ex (fun x hx => hexJ x hx)
      (entIn_latS_of_eq (t := sC * sD) (by ring) (Subring.mul_mem _ hsCO hsDO) hG)
  have X1 : EntIn (latS L c1) (ex • (h1i * (l : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by rw [E1]; exact entIn_sandwich hsA hsB hD1
  have hD2 : EntIn (latS L (sC * (sD * c1))) (ey • D).transpose :=
    entIn_transpose (entIn_smul ey (fun x hx => heyJ x hx)
      (entIn_latS_of_eq (t := sA * sB) (by ring) (Subring.mul_mem _ hsAO hsBO) hG))
  have Y2 : EntIn (latS L c1) (ey • ((ρ : Matrix (Fin n) (Fin n) L.Ep) * h2i - 1)) := by rw [E2]; exact entIn_sandwich hsC hsD hD2

  set k1 : GL (Fin n) L.Ep := h1⁻¹ * l with hk1d
  set k2 : GL (Fin n) L.Ep := ρ * h2⁻¹ with hk2d
  set k1i := ((k1⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hk1id
  set k2i := ((k2⁻¹ : GL (Fin n) L.Ep) : Matrix (Fin n) (Fin n) L.Ep) with hk2id
  have R : (k1 : Matrix (Fin n) (Fin n) L.Ep) * N * (k2 : Matrix (Fin n) (Fin n) L.Ep) = N := by
    rw [hk1v, hk2v]
    calc h1i * (l : Matrix (Fin n) (Fin n) L.Ep) * N * ((ρ : Matrix (Fin n) (Fin n) L.Ep) * h2i) =
          h1i * ((l : Matrix (Fin n) (Fin n) L.Ep) * N * (ρ : Matrix (Fin n) (Fin n) L.Ep)) * h2i := by
          simp only [Matrix.mul_assoc]
      _ = h1i * ((h1 : Matrix (Fin n) (Fin n) L.Ep) * N * (h2 : Matrix (Fin n) (Fin n) L.Ep)) * h2i := by
          rw [hlN, hh]
      _ = (h1i * h1) * N * ((h2 : Matrix (Fin n) (Fin n) L.Ep) * h2i) := by simp only [Matrix.mul_assoc]
      _ = N := by rw [h11, h22, Matrix.one_mul, Matrix.mul_one]
  have hk1i : k1i * (k1 : Matrix (Fin n) (Fin n) L.Ep) = 1 := by
    rw [hk1id, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hk2i : (k2 : Matrix (Fin n) (Fin n) L.Ep) * k2i = 1 := by
    rw [hk2id, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have S2 : (k2 : Matrix (Fin n) (Fin n) L.Ep) = Ni * k1i * N := by
    calc (k2 : Matrix (Fin n) (Fin n) L.Ep) = Ni * (k1i * ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2)) := by
          rw [show k1i * ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) = (k1i * k1) * N * k2 by
            simp only [Matrix.mul_assoc], hk1i, Matrix.one_mul, ← Matrix.mul_assoc, hN', Matrix.one_mul]
      _ = Ni * k1i * N := by rw [R, Matrix.mul_assoc]
  have S1 : (k1 : Matrix (Fin n) (Fin n) L.Ep) = N * k2i * Ni := by
    calc (k1 : Matrix (Fin n) (Fin n) L.Ep) = (((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) * k2i) * Ni := by
          rw [show ((k1 : Matrix (Fin n) (Fin n) L.Ep) * N * k2) * k2i = k1 * N * (k2 * k2i) by
            simp only [Matrix.mul_assoc], hk2i, Matrix.mul_one, Matrix.mul_assoc, hN, Matrix.mul_one]
      _ = N * k2i * Ni := by rw [R]
  have F1 : ex • ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1) = Ni * (ex • (k1i - 1)) * N := by
    rw [smul_sandwich, S2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hN']
  have F2 : ey • ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1) = N * (ey • (k2i - 1)) * Ni := by
    rw [smul_sandwich, S1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hN]

  have hJ : ∀ x ∈ latS L c1, ∀ y ∈ latS L c1, x * y ∈ latS L c1 := fun x hx y hy => latS_mul_self hc1O hx hy
  have I1 : EntIn (latS L c1) (ex • (k1i - 1)) := by
    refine proj_inv (fun i => i.val) (fun i => i.isLt) hJ ex hxx k1 (fun i j h => hk1 i j (Fin.le_def.2 h)) ?_
    rw [hk1v]; exact X1
  have I2 : EntIn (latS L c1) (ey • (k2i - 1)) := by
    refine proj_inv (fun i => n - 1 - i.val) (fun i => by have := i.isLt; omega) hJ ey hyy k2
      (fun i j h => hk2 i j (Fin.le_def.2 (by have := i.isLt; have := j.isLt; omega))) ?_
    rw [hk2v]; exact Y2
  have G1 : EntIn (latS L c) (ex • ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by
    rw [F1]; exact entIn_sandwich hsNi hsN I1
  have G2 : EntIn (latS L c) (ey • ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)) := by
    rw [F2]
    exact entIn_sandwich hsN hsNi (entIn_latS_of_eq (t := 1) (by rw [hc1]; ring) (Subring.one_mem _) I2)
  have hsplit : ∀ X : Matrix (Fin n) (Fin n) L.Ep, X = ex • X + ey • X := fun X => by
    rw [← add_smul, hsum, one_smul]
  refine ⟨?_, ?_⟩
  · show EntIn (latS L c) ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)
    rw [hsplit ((k1 : Matrix (Fin n) (Fin n) L.Ep) - 1)]
    refine entIn_add ?_ G2
    rw [hk1v]
    exact entIn_latS_of_eq (t := sNi * sN) (by rw [hc1]; ring) (Subring.mul_mem _ hsNiO hsNO) X1
  · show EntIn (latS L c) ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)
    rw [hsplit ((k2 : Matrix (Fin n) (Fin n) L.Ep) - 1)]
    refine entIn_add G1 ?_
    rw [hk2v]
    exact entIn_latS_of_eq (t := sNi * sN) (by rw [hc1]; ring) (Subring.mul_mem _ hsNiO hsNO) Y2

end Close2

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section At

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

def ellP (p : PlF D) : (D.s.atP p).Fp := ((Loc.resChar p : ℕ) : (D.s.atP p).Fp)

theorem ellP_ne (p : PlF D) : ellP p ≠ 0 := by
  have := (D.s.atP p).char0
  have hp := (D.s.atP p).ellPrime.out
  exact Nat.cast_ne_zero.2 hp.ne_zero

theorem ellP_mem (p : PlF D) : ellP p ∈ 𝒪[(D.s.atP p).Fp] := natCast_mem _ _

variable {M δ}

theorem latS_R {p : PlF D} (hA : Agree δ M p) {x : (D.s.atP p).Ep} (hx : x ∈ latS (D.s.atP p) (ellP p)) :
    x ∈ (M p).R := by
  obtain ⟨y, hy, rfl⟩ := mem_latS.1 hx
  obtain ⟨-, -, -, hO, -, hsp⟩ := hA
  show _ ∈ (⟨(M p).L, (M p).split, (M p).mu⟩ : Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep).R
  rcases hM : (M p).split with _ | g
  · show _ ∈ (M p).L.O
    rw [hO]
    exact (D.s.atP p).O.mul_mem (alg_mem_O (ellP_mem p)) hy
  · rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      rw [Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split]
      have hy' := (Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg y).1 hy
      have hq : ((g.q : 𝒪[(D.s.atP p).Fp]) : (D.s.atP p).Fp) = ellP p := by rw [hsp'.2]; exact sg.q_eq
      have he : g.e (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (ellP p) * y) =
          (ellP p * (sg.e y).1, ellP p * (sg.e y).2) := by
        rw [map_mul, AlgEquiv.commutes, hsp'.1]; rfl
      rw [he]
      refine ⟨Subring.mul_mem _ (ellP_mem p) hy'.1, Subring.mul_mem _ (ellP_mem p) hy'.2,
        (sg.e y).1 - (sg.e y).2, Subring.sub_mem _ hy'.1 hy'.2, ?_⟩
      rw [hq]; ring

variable (M δ)

theorem ptMat_mono : ptMat w = mono (Formalism.L2.SG.Pf.fσ w) (fun a => Formalism.L2.SG.Pf.pv w.1 a) := by
  ext a b
  rw [Formalism.L2.SG.Pf.ptMat_fσ]
  rfl

theorem exists_unit_monomial_stable_of_Y0 {p : PlF D} (hA : Agree δ M p) :
    ∃ N Ni : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, N * Ni = 1 ∧ Ni * N = 1 ∧
      (∃ ν : Fin (D.R.rS + 1) → (D.s.atP p).Ep, (∀ a, IsUnit (ν a)) ∧ N = mono (Formalism.L2.SG.Pf.fσ w) ν) ∧
      ∀ l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep, IsLoUni l → IsUpUni ρ →
        l * ProdE.Y0 M δ u u' w p * ρ = ProdE.Y0 M δ u u' w p → l * N * ρ = N := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  obtain ⟨ν, hν, κ, hY⟩ := zzp_mono δ M u u' hA hσ (fun a => (-1) ^ (D.R.rS - (σ a).val) * Formalism.L2.SG.Pf.pv w.1 a)
    (fun a => mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (Formalism.L2.SG.Pf.pv_ne' w a))
  have hY0 : ProdE.Y0 M δ u u' w p = mono σ ν - Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS) κ := by
    rw [← hY]
    unfold ProdE.Y0
    rw [ptMat_mono, zhatOM_mono]
  refine ⟨mono σ ν, mono σ (fun a => Ring.inverse (ν (σ a))), ?_, ?_, ⟨ν, hν, rfl⟩, ?_⟩
  · ext i j
    rw [mono_mul]
    simp only [mono, Matrix.of_apply, Matrix.one_apply, hσ]
    split_ifs with h1 h2 h2
    · exact Ring.mul_inverse_cancel _ (hν i)
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · simp
  · ext i j
    rw [mul_mono hσ]
    simp only [mono, Matrix.of_apply, hσ, Matrix.one_apply]
    by_cases h : σ j = σ i
    · have hij : i = j := by rw [← hσ i, ← h, hσ]
      subst hij
      simp only [if_true]
      exact Ring.inverse_mul_cancel _ (hν _)
    · have hij : i ≠ j := fun e => h (by rw [e])
      rw [if_neg h, if_neg hij, zero_mul]
  · intro l ρ hl hρ h
    rw [hY0] at h
    exact fix_of_fix hl hρ κ h

end At

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cong

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem one_mem_R {p : PlF D} (a b : Fin (D.R.rS + 1)) :
    (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b ∈ (M p).R := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (M p).R.one_mem
  · exact (M p).R.zero_mem

theorem mem_R_of_sub_one {p : PlF D} (hA : Agree δ M p) {X : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep}
    (h : EntIn (latS (D.s.atP p) (ellP p)) (X - 1)) (a b : Fin (D.R.rS + 1)) : X a b ∈ (M p).R := by
  have e : X a b = (X - 1) a b + (1 : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) a b := by
    rw [Matrix.sub_apply]; ring
  rw [e]
  exact (M p).R.add_mem (latS_R hA (h a b)) (one_mem_R M a b)

theorem cong_at {p : PlF D} (hA : Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U) :
    ∃ c : (D.s.atP p).Fp, c ≠ 0 ∧ c ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ k : ProdE.StP M δ u u' w p,
      EntIn (latS (D.s.atP p) c) ((k.1.1 : ProdE.MP p) - 1) → EntIn (latS (D.s.atP p) c) ((k.1.2.unop : ProdE.MP p) - 1) →
        k ∈ ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w hA L U hL hU := by
  set Lp := lOf δ M p L U
  set Lpi := lOf δ M p L⁻¹ U⁻¹
  set Up := ρOf δ M p L U
  set Upi := ρOf δ M p L⁻¹ U⁻¹
  have hLi := ZsVolGrp.isLoUni_inv hL
  have hUi := ZsVolGrp.isUpUni_inv hU
  have hLL : Lp * Lpi = 1 := by
    rw [← lOf_mul δ M hA, hLi.2.2, hUi.2.1, lOf_one δ M hA]
  have hUU : Upi * Up = 1 := by
    rw [← ρOf_mul δ M hA, hLi.2.2, hUi.2.1, ρOf_one δ M hA]
  have hLp := ProdE.lOf_loUni M δ hA L U hL hU
  have hLpi := ProdE.lOf_loUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  have hUp := ProdE.ρOf_upUni M δ hA L U hL hU
  have hUpi := ProdE.ρOf_upUni M δ hA L⁻¹ U⁻¹ hLi.1 hUi.1
  obtain ⟨s1, hs10, hs1O, hs1⟩ := bounded_mat (L := D.s.atP p) Lp
  obtain ⟨s2, hs20, hs2O, hs2⟩ := bounded_mat (L := D.s.atP p) Lpi
  obtain ⟨s3, hs30, hs3O, hs3⟩ := bounded_mat (L := D.s.atP p) Up
  obtain ⟨s4, hs40, hs4O, hs4⟩ := bounded_mat (L := D.s.atP p) Upi
  refine ⟨ellP p * (s1 * s2 * s3 * s4),
    mul_ne_zero (ellP_ne p) (mul_ne_zero (mul_ne_zero (mul_ne_zero hs10 hs20) hs30) hs40),
    Subring.mul_mem _ (ellP_mem p) (Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O),
    fun k h1 h2 => ?_⟩
  obtain ⟨hk1, hk2, -⟩ := k.2
  have hO12 : s1 * s2 * s3 * s4 ∈ 𝒪[(D.s.atP p).Fp] :=
    Subring.mul_mem _ (Subring.mul_mem _ (Subring.mul_mem _ hs1O hs2O) hs3O) hs4O
  have h1l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.1 : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h1
  have h2l : EntIn (latS (D.s.atP p) (ellP p)) ((k.1.2.unop : ProdE.MP p) - 1) :=
    entIn_latS_of_eq (t := s1 * s2 * s3 * s4) rfl hO12 h2
  have h1c : EntIn (latS (D.s.atP p) (ellP p)) (Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi) :=
    entIn_sandwich hs1 hs2 (entIn_latS_of_eq (t := s3 * s4) (by ring) (Subring.mul_mem _ hs3O hs4O) h1)
  have h2c : EntIn (latS (D.s.atP p) (ellP p)) (Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up) :=
    entIn_sandwich hs4 hs3 (entIn_latS_of_eq (t := s1 * s2) (by ring) (Subring.mul_mem _ hs1O hs2O) h2)
  have e1 : Lp * (k.1.1 : ProdE.MP p) * Lpi - 1 = Lp * ((k.1.1 : ProdE.MP p) - 1) * Lpi := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hLL]
  have e2 : Upi * (k.1.2.unop : ProdE.MP p) * Up - 1 = Upi * ((k.1.2.unop : ProdE.MP p) - 1) * Up := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hUU]
  have hc1 := ZsVolGrp.isLoUni_mul (ZsVolGrp.isLoUni_mul hLp hk1) hLpi
  have hc2 := ZsVolGrp.isUpUni_mul (ZsVolGrp.isUpUni_mul hUpi hk2) hUp
  refine Subgroup.mem_inf.2 ⟨⟨⟨fun a => (hk1 a a).2 rfl, fun a b h => (hk1 a b).1 h,
    mem_R_of_sub_one M δ hA h1l⟩, ⟨fun a => (hk2 a a).2 rfl, fun a b h => (hk2 a b).1 h, mem_R_of_sub_one M δ hA h2l⟩⟩,
    ⟨⟨fun a => (hc1 a a).2 rfl, fun a b h => (hc1 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e1]; exact h1c)⟩,
    ⟨fun a => (hc2 a a).2 rfl, fun a b h => (hc2 a b).1 h, mem_R_of_sub_one M δ hA (by rw [e2]; exact h2c)⟩⟩⟩

end Cong

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Split

variable {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ}

theorem smul_eq_of_cx (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cx e X = cx e Y) :
    e.symm (1, 0) • X = e.symm (1, 0) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cx, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe] at this
  ext
  · simp [this]
  · simp

theorem smul_eq_of_cy (e : K ≃ₐ[F] F × F) {X Y : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : cy e X = cy e Y) :
    e.symm (0, 1) • X = e.symm (0, 1) • Y := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  apply e.injective
  rw [map_mul, map_mul, AlgEquiv.apply_symm_apply]
  have := congrFun (congrFun h i) j
  simp only [cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe] at this
  ext
  · simp
  · simp [this]

theorem cx_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cx e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cx, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

theorem cy_diag (e : K ≃ₐ[F] F × F) (d : Fin (r + 1) → F) :
    cy e (Matrix.diagonal fun i => algebraMap F K (d i)) = Matrix.diagonal d := by
  ext i j
  simp only [cy, Matrix.map_apply, Matrix.diagonal_apply, RingHom.comp_apply, RingHom.coe_snd, RingHom.coe_coe]
  split_ifs <;> simp [AlgEquiv.commutes]

end Split

section Data

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp)

theorem mode_data {p : PlF D} (hA : Agree δ M p) :
    ∃ (ex ey : (D.s.atP p).Ep) (d di gg ggi : Fin (D.R.rS + 1) → (D.s.atP p).Ep),
      ex ∈ (D.s.atP p).O ∧ ey ∈ (D.s.atP p).O ∧ ex * ex = ex ∧ ey * ey = ey ∧ ex + ey = 1 ∧ ex * ey = 0 ∧
      (∀ i, d i * di i = 1) ∧ (∀ i, gg i * ggi i = 1) ∧
      ∀ a b : Formalism.L2.SG.PairVal.MatR D,
        ex • lOf δ M p a b = ex • (Matrix.diagonal d * a.map (D.s.atP p).ιE * Matrix.diagonal di) ∧
        ey • ρOf δ M p a b = ey • (Matrix.diagonal ggi * (a.map (D.s.atP p).ιE).transpose * Matrix.diagonal gg) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := id hA
  cases hM : (M p).split with
  | none =>
    refine ⟨1, 0, fun i => (M p).L.cj (frFac δ p i), fun i => Ring.inverse ((M p).L.cj (frFac δ p i)),
      fun _ => 1, fun _ => 1, (D.s.atP p).O.one_mem, (D.s.atP p).O.zero_mem, mul_one 1, mul_zero 0, add_zero 1,
      mul_zero 1, fun i => Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _), fun _ => mul_one 1, fun a b => ⟨?_, ?_⟩⟩
    · simp only [lOf, hM, one_smul]
      exact lL_eq _ _ _ a
    · simp only [zero_smul]
  | some g =>
    rcases hR : (D.s.atP p).split with _ | sg
    · simp [hM, hR] at hsp
    · have hsp' : g.e = sg.e ∧ g.q = sg.q := by simpa [hM, hR] using hsp
      have hx := fun i => (split_units δ M hA g i).1
      have hy := fun i => (split_units δ M hA g i).2
      have hmemO : ∀ a b : (D.s.atP p).Fp, a ∈ 𝒪[(D.s.atP p).Fp] → b ∈ 𝒪[(D.s.atP p).Fp] →
          g.e.symm (a, b) ∈ (D.s.atP p).O := by
        intro a b ha hb
        rw [Formalism.MainNotions.BridgeLemma.O_split (D.s.atP p) sg, ← hsp'.1, AlgEquiv.apply_symm_apply]
        exact ⟨ha, hb⟩
      refine ⟨g.e.symm (1, 0), g.e.symm (0, 1),
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).2), fun i => algebraMap _ _ ((g.e (frFac δ p i)).2)⁻¹,
        fun i => algebraMap _ _ ((g.e (frFac δ p i)).1), fun i => algebraMap _ _ ((g.e (frFac δ p i)).1)⁻¹,
        hmemO 1 0 (Subring.one_mem _) (Subring.zero_mem _), hmemO 0 1 (Subring.zero_mem _) (Subring.one_mem _),
        ?_, ?_, ?_, ?_, fun i => by rw [← map_mul, mul_inv_cancel₀ (hy i), map_one],
        fun i => by rw [← map_mul, mul_inv_cancel₀ (hx i), map_one], fun a b => ⟨?_, ?_⟩⟩
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · apply g.e.injective; simp
      · simp only [lOf, hM]
        apply smul_eq_of_cx
        rw [cx_lG, cx_mul, cx_mul, cx_diag, cx_diag]
        rfl
      · simp only [ρOf, hM]
        apply smul_eq_of_cy
        rw [cy_ρG, cy_mul, cy_mul, cy_diag, cy_diag]
        rfl

end Data

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section CloseAt

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem diag_mul_diag_apply {K : Type*} [CommRing K] {n : ℕ} (a b : Fin n → K) (X : Matrix (Fin n) (Fin n) K)
    (i j : Fin n) : (Matrix.diagonal a * X * Matrix.diagonal b) i j = a i * X i j * b j := by
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

set_option maxHeartbeats 800000 in
theorem close_at {p : PlF D} (hA : Agree δ M p) (h : ProdE.StP M δ u u' w p) (c : (D.s.atP p).Fp) (hc0 : c ≠ 0)
    (hc : c ∈ 𝒪[(D.s.atP p).Fp]) :
    ∃ τ : ProdE.MP p, (∀ i j, i < j → τ i j = 0) ∧ (∀ i, τ i i = 1) ∧
      (∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → τ i j = 0) ∧
      ∃ c' : (D.s.atP p).Fp, c' ≠ 0 ∧ c' ∈ 𝒪[(D.s.atP p).Fp] ∧ ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
        EntIn (latS (D.s.atP p) c') (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ) →
        EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.1 : ProdE.MP p) - 1) ∧
          EntIn (latS (D.s.atP p) c) (((h⁻¹ * ProdE.πP M δ u u' w hA g).1.2.unop : ProdE.MP p) - 1) := by
  obtain ⟨ex, ey, d, di, gg, ggi, hexO, heyO, hxx, hyy, hsum, hxy, hd, hg, hlin⟩ := mode_data M δ hA
  obtain ⟨N, Ni, hN, hN', ⟨ν, hν, hNν⟩, hfix⟩ := exists_unit_monomial_stable_of_Y0 M δ u u' w hA
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  have hσ : ∀ a, σ (σ a) = a := Formalism.L2.SG.Pf.fσ_fσ w
  set h1 : ProdE.GLp p := h.1.1 with hh1d
  set h2 : ProdE.GLp p := h.1.2.unop with hh2d
  obtain ⟨hh1, hh2, hh3⟩ := h.2
  have hh : (h1 : ProdE.MP p) * N * (h2 : ProdE.MP p) = N := hfix _ _ hh1 hh2 hh3
  obtain ⟨hi1, hi2, -⟩ := (h⁻¹).2
  have hΔ : Matrix.diagonal d * Matrix.diagonal di = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hd i
  have hΓ : Matrix.diagonal gg * Matrix.diagonal ggi = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; exact hg i
  have hΓ' : Matrix.diagonal ggi * Matrix.diagonal gg = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; rw [mul_comm]; exact hg i
  obtain ⟨c', hc'0, hc'O, hcl⟩ := close ex ey hexO heyO hxx hyy hsum hxy N Ni (Matrix.diagonal d) (Matrix.diagonal di)
    (Matrix.diagonal gg) (Matrix.diagonal ggi) hN hN' hΔ hΓ hΓ' h1 h2 hh c hc0 hc

  have h1inv : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * (h1 : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2inv : (h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have rel1 : (h1 : ProdE.MP p) * mono σ ν = mono σ ν * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by
    rw [← hNν]
    calc (h1 : ProdE.MP p) * N = (h1 : ProdE.MP p) * N * ((h2 : ProdE.MP p) * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p)) := by
          rw [h2inv, Matrix.mul_one]
      _ = N * ((h2⁻¹ : ProdE.GLp p) : ProdE.MP p) := by rw [← Matrix.mul_assoc, hh]
  have rel2 : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * mono σ ν = mono σ ν * (h2 : ProdE.MP p) := by
    rw [← hNν]
    calc ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * N
        = ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) * ((h1 : ProdE.MP p) * N * (h2 : ProdE.MP p)) := by rw [hh]
      _ = N * (h2 : ProdE.MP p) := by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1inv, Matrix.one_mul]
  refine ⟨ex • (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) +
      ey • (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi).transpose, ?_, ?_, ?_, c', hc'0, hc'O, ?_⟩
  · intro i j hij
    have a1 : (h1 : ProdE.MP p) i j = 0 := (hh1 i j).1 hij
    have a2 : (h2 : ProdE.MP p) j i = 0 := (hh2 j i).1 hij
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, a1, a2]
    simp
  · intro i
    have a1 : (h1 : ProdE.MP p) i i = 1 := (hh1 i i).2 rfl
    have a2 : (h2 : ProdE.MP p) i i = 1 := (hh2 i i).2 rfl
    have t1 : (Matrix.diagonal di * (h1 : ProdE.MP p) * Matrix.diagonal d) i i = 1 := by
      rw [diag_mul_diag_apply, a1, mul_one, mul_comm, hd i]
    have t2 : (Matrix.diagonal gg * (h2 : ProdE.MP p) * Matrix.diagonal ggi) i i = 1 := by
      rw [diag_mul_diag_apply, a2, mul_one, hg i]
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, t1, t2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one, hsum]
  · intro i j hij
    have e1 : (h1 : ProdE.MP p) i j = 0 :=
      fix_pat hσ ν hν (fun a b hab => (hi2 a b).1 hab) rel1 i j hij
    have e2 : (h2 : ProdE.MP p) j i = 0 := by
      have z : ((h1⁻¹ : ProdE.GLp p) : ProdE.MP p) (σ j) (σ i) = 0 := (hi1 (σ j) (σ i)).1 hij
      have := fix_entry hσ ν rel2 (σ j) (σ i)
      rw [hσ, hσ, z, zero_mul] at this
      exact (hν (σ j)).mul_right_eq_zero.1 this.symm
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.transpose_apply, diag_mul_diag_apply,
      diag_mul_diag_apply, e1, e2]
    simp
  · intro g hG
    set π := ProdE.πP M δ u u' w hA g with hπd
    set l : ProdE.GLp p := π.1.1 with hld
    set ρ : ProdE.GLp p := π.1.2.unop with hρd
    obtain ⟨hk1, hk2, -⟩ := (h⁻¹ * π).2
    obtain ⟨hπl, hπρ, hπ⟩ := π.2
    have ek1 : ((h⁻¹ * π).1.1 : ProdE.GLp p) = h1⁻¹ * l := rfl
    have ek2 : ((h⁻¹ * π).1.2.unop : ProdE.GLp p) = ρ * h2⁻¹ := rfl
    have hk1' : Formalism.MainNotions.S.IsLoUni (((h1⁻¹ * l : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek1]; exact hk1
    have hk2' : Formalism.MainNotions.S.IsUpUni (((ρ * h2⁻¹ : ProdE.GLp p)) : ProdE.MP p) := by rw [← ek2]; exact hk2
    have hl : ex • ((l : ProdE.GLp p) : ProdE.MP p) =
        ex • (Matrix.diagonal d * ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE *
          Matrix.diagonal di) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).1
    have hρ : ey • ((ρ : ProdE.GLp p) : ProdE.MP p) =
        ey • (Matrix.diagonal ggi * (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map
          (D.s.atP p).ιE).transpose * Matrix.diagonal gg) :=
      (hlin (g : Formalism.L2.SG.PairVal.GLR D) (Formalism.L2.SG.Pf.VolPinAsm.bOf w g)).2
    have hlN : ((l : ProdE.GLp p) : ProdE.MP p) * N * ((ρ : ProdE.GLp p) : ProdE.MP p) = N := hfix _ _ hπl hπρ hπ
    have res := hcl l ρ (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE)
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk1' i j).1 h', Matrix.one_apply_ne (ne_of_lt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk1' i i).2 rfl, Matrix.one_apply_eq, sub_self])
      (fun i j hij => by
        rcases lt_or_eq_of_le hij with h' | h'
        · rw [Matrix.sub_apply, (hk2' i j).1 h', Matrix.one_apply_ne (ne_of_gt h'), sub_zero]
        · subst h'
          rw [Matrix.sub_apply, (hk2' j j).2 rfl, Matrix.one_apply_eq, sub_self])
      hlN hl hρ hG
    rw [ek1, ek2]
    exact res

end CloseAt

end Formalism.L2.SG.Pf.ProdEApprox
end
end

noncomputable section

open IsDedekindDomain NumberField ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.Pf.StabShape

namespace Formalism.L2.SG.Pf.ProdEApprox

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1))

theorem mem_stSet_of_pat (a : Formalism.L2.SG.PairVal.MatR D) (ha : IsLoUni a)
    (hpat : ∀ i j, Formalism.L2.SG.Pf.fσ w j < Formalism.L2.SG.Pf.fσ w i → a i j = 0) :
    ∃ b : Formalism.L2.SG.PairVal.MatR D, IsUpUni b ∧ a * ptMat w * b = ptMat w := by
  set σ := Formalism.L2.SG.Pf.fσ w
  have hσ : ∀ x, σ (σ x) = x := Formalism.L2.SG.Pf.fσ_fσ w
  set ν : Fin (D.R.rS + 1) → D.host.E := fun x => Formalism.L2.SG.Pf.pv w.1 x
  have hν : ∀ x, IsUnit (ν x) := fun x => isUnit_iff_ne_zero.2 (Formalism.L2.SG.Pf.pv_ne' w x)
  have hfix := fix_cOf hσ ν hν a
  obtain ⟨hc1, hc2⟩ := cOf_up hσ ν a (fun i => (ha i i).2 rfl) hpat hν
  have hcU : IsUpUni (cOf σ ν a) := fun i j => ⟨fun h => hc2 i j h, fun h => by subst h; exact hc1 i⟩
  obtain ⟨hbU, -, hcb⟩ := ZsVolGrp.isUpUni_inv hcU
  refine ⟨(cOf σ ν a)⁻¹, hbU, ?_⟩
  rw [ptMat_mono, hfix, Matrix.mul_assoc, hcb, Matrix.mul_one]

theorem approx_core (hA : ∀ p, Agree δ M p) (L U : Formalism.L2.SG.PairVal.MatR D) (hL : IsLoUni L) (hU : IsUpUni U)
    (S : Finset (PlF D))
    (hS : ∀ p, p ∉ S → ∀ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ i j, (D.s.atP p).ιE (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) i j) ∈ (D.s.atP p).O) →
        ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p)
    (h : ∀ p, ProdE.StP M δ u u' w p) :
    ∃ g : Formalism.L2.SG.Pf.VolPinAsm.StG w,
      (∀ p ∈ S, (h p)⁻¹ * ProdE.πP M δ u u' w (hA p) g ∈
        ProdE.AP M δ u u' w p ⊓ ProdE.CPL M δ u u' w (hA p) L U hL hU) ∧
      ∀ p, p ∉ S → ProdE.πP M δ u u' w (hA p) g ∈ ProdE.AP M δ u u' w p := by
  classical
  set σ := Formalism.L2.SG.Pf.fσ w with hσd
  choose c hc0 hcO hcong using fun p => cong_at M δ u u' w (hA p) L U hL hU
  choose τ hτ1 hτ2 hτ3 c' hc'0 hc'O hcl using fun p => close_at M δ u u' w (hA p) (h p) (c p) (hc0 p) (hcO p)
  choose t ht1 ht2 using fun ij : Fin (D.R.rS + 1) × Fin (D.R.rS + 1) =>
    sa_lat (fun p => D.s.atP p) S (fun p => τ p ij.1 ij.2) c' (fun p _ => hc'0 p)
  set a : Formalism.L2.SG.PairVal.MatR D := fun i j =>
    if j < i ∧ σ i < σ j then t (i, j) else (1 : Formalism.L2.SG.PairVal.MatR D) i j with had
  have ha : IsLoUni a := by
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.1 (not_lt.2 hij.le)
      simp only [had, if_neg this]
      exact Matrix.one_apply_ne (ne_of_lt hij)
    · subst hij
      have : ¬ (i < i ∧ σ i < σ i) := fun h' => lt_irrefl _ h'.1
      simp only [had, if_neg this, Matrix.one_apply_eq]
  have hpat : ∀ i j, σ j < σ i → a i j = 0 := by
    intro i j hij
    have hne : i ≠ j := fun e => by subst e; exact lt_irrefl _ hij
    have : ¬ (j < i ∧ σ i < σ j) := fun h' => absurd h'.2 (not_lt.2 hij.le)
    simp only [had, if_neg this]
    exact Matrix.one_apply_ne hne
  have hdet : IsUnit a.det := by rw [ZsVolGrp.det_lo (fun x => (ha x x).2 rfl) (fun x y hxy => (ha x y).1 hxy)]; exact isUnit_one
  obtain ⟨b, hb, hab⟩ := mem_stSet_of_pat w a ha hpat
  let gGL : Formalism.L2.SG.PairVal.GLR D := Matrix.nonsingInvUnit a hdet
  have hgv : (gGL : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  let g : Formalism.L2.SG.Pf.VolPinAsm.StG w := ⟨gGL, ⟨by rw [hgv]; exact ha, b, hb, by rw [hgv]; exact hab⟩⟩
  have hgv' : ((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D) = a := rfl
  refine ⟨g, fun p hp => ?_, fun p hp => hS p hp g ?_⟩
  · have hclose : EntIn (latS (D.s.atP p) (c' p))
        (((g : Formalism.L2.SG.PairVal.GLR D) : Formalism.L2.SG.PairVal.MatR D).map (D.s.atP p).ιE - τ p) := by
      intro i j
      rw [hgv', Matrix.sub_apply, Matrix.map_apply]
      by_cases hz : j < i ∧ σ i < σ j
      · simp only [had, if_pos hz]
        exact mem_latS.2 (ht1 (i, j) p hp)
      · simp only [had, if_neg hz]
        have e : (D.s.atP p).ιE ((1 : Formalism.L2.SG.PairVal.MatR D) i j) - τ p i j = 0 := by
          rcases lt_trichotomy i j with hij | hij | hij
          · rw [Matrix.one_apply_ne (ne_of_lt hij), map_zero, hτ1 p i j hij, sub_zero]
          · subst hij; rw [Matrix.one_apply_eq, map_one, hτ2 p i, sub_self]
          · have hs : σ j < σ i := by
              rcases lt_or_gt_of_ne (fun e : σ i = σ j => (ne_of_gt hij) (by
                rw [← Formalism.L2.SG.Pf.fσ_fσ w i, ← Formalism.L2.SG.Pf.fσ_fσ w j]; exact congrArg _ e)) with h' | h'
              · exact absurd ⟨hij, h'⟩ hz
              · exact h'
            rw [Matrix.one_apply_ne (ne_of_gt hij), map_zero, hτ3 p i j hs, sub_zero]
        rw [e]; exact (latS (D.s.atP p) (c' p)).zero_mem
    obtain ⟨h1, h2⟩ := hcl p g hclose
    exact hcong p _ h1 h2
  · intro i j
    rw [hgv']
    by_cases hz : j < i ∧ σ i < σ j
    · simp only [had, if_pos hz]
      exact ht2 (i, j) p hp
    · simp only [had, if_neg hz]
      rw [Matrix.one_apply]
      split_ifs
      · rw [map_one]; exact (D.s.atP p).O.one_mem
      · rw [map_zero]; exact (D.s.atP p).O.zero_mem

end Main

end Formalism.L2.SG.Pf.ProdEApprox
