module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.Comp1IdentityLeft
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonA
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.BilinearPartAx3
noncomputable section

namespace PositivityTheory.HtPt.Ca

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

variable {R : Type} [CommRing R] {d : ℕ}

open ReciprocityTheory.ChartRestriction.G.TB.Canon in
theorem coeff_ax3_vanish {f : PS R 3 d} (hf : Ax3 f) (D : Fin 3 × Fin d →₀ ℕ) (hD : D ≠ 0) (k : Fin 3)
    (hk : ∀ b, D (k, b) = 0) : coeff D f = 0 := by
  obtain ⟨h0, h1, h2⟩ := hf
  have h := coeff_kill k f D
  rw [if_pos hk, sb_apply] at h
  rw [← h]
  convert (show coeff D (1 : PS R 3 d) = 0 by rw [coeff_one, if_neg hD]) using 2
  fin_cases k
  · convert eval3_axiom_zero h0 (Z_pt (R := R) (d := d) (n := 3) 1) (Z_pt 2) using 2
    funext j
    fin_cases j <;> simp [Function.update, gen]
  · convert eval3_axiom_one h1 (Z_pt (R := R) (d := d) (n := 3) 0) (Z_pt 2) using 2
    funext j
    fin_cases j <;> simp [Function.update, gen]
  · convert eval3_axiom_two h2 (Z_pt (R := R) (d := d) (n := 3) 0) (Z_pt 1) using 2
    funext j
    fin_cases j <;> simp [Function.update, gen]

theorem exists_third (a b : Fin 3) : ∃ k, a ≠ k ∧ b ≠ k := by revert a b; decide

theorem bilinear_part_ax3 {f : PS R 3 d} (hf : Ax3 f) {a : Fin 3 → Pt R 2 d} (ha : ZZ a) : bil (ev a f) 1 1 = 0 := by
  have h1 : ∀ p : Fin 3 × Fin d, constantCoeff ((pderiv p) f) = 0 := by
    intro p
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    obtain ⟨k, hk, -⟩ := exists_third p.1 p.1
    rw [coeff_ax3_vanish hf _ (by simp) k ?_, zero_mul]
    intro b
    rw [Finsupp.single_apply, if_neg]
    rintro rfl
    exact hk rfl
  have h2 : ∀ p q : Fin 3 × Fin d, constantCoeff ((pderiv q) ((pderiv p) f)) = 0 := by
    intro p q
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, coeff_pderiv]
    obtain ⟨k, hk1, hk2⟩ := exists_third p.1 q.1
    rw [coeff_ax3_vanish hf _ (by simp) k ?_, zero_mul, zero_mul]
    intro b
    have e1 : (Finsupp.single q 1 : Fin 3 × Fin d →₀ ℕ) (k, b) = 0 := by
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hk2 rfl
    have e2 : (Finsupp.single p 1 : Fin 3 × Fin d →₀ ℕ) (k, b) = 0 := by
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hk1 rfl
    rw [Finsupp.add_apply, e1, e2]
  ext i j
  rw [bil_dd, cc_dd_ev ha _ _ f h1]
  simp [h2]

theorem axOne_compL {f : PS R 2 d} (hf : AxOne f) {φ : Pt R 1 d} (hφ : Z φ) :
    AxOne (ev (n := 2) ![comp1 φ (pt R d 0), pt R d 1] f) := by
  have h := axOne_comp hf hφ (Z_pt (0 : Fin 1))
  rwa [comp1_identity_left] at h

theorem axOne_compR {f : PS R 2 d} (hf : AxOne f) {φ : Pt R 1 d} (hφ : Z φ) :
    AxOne (ev (n := 2) ![pt R d 0, comp1 φ (pt R d 1)] f) := by
  have h := axOne_comp hf (Z_pt (0 : Fin 1)) hφ
  rwa [comp1_identity_left] at h

theorem bil_compL {f : PS R 2 d} (hf : AxOne f) {φ : Pt R 1 d} (hφ : Z φ) :
    bil (ev (n := 2) ![comp1 φ (pt R d 0), pt R d 1] f) 1 1 = (lin φ 1).transpose * bil f 1 1 := by
  have h := bil_comp hf hφ (Z_pt (R := R) (d := d) (n := 1) 0)
  rw [comp1_identity_left] at h
  rw [h, (lin_comp R d φ φ hφ hφ).2.1, Matrix.mul_one]

theorem bil_compR {f : PS R 2 d} (hf : AxOne f) {φ : Pt R 1 d} (hφ : Z φ) :
    bil (ev (n := 2) ![pt R d 0, comp1 φ (pt R d 1)] f) 1 1 = bil f 1 1 * lin φ 1 := by
  have h := bil_comp hf (Z_pt (R := R) (d := d) (n := 1) 0) hφ
  rw [comp1_identity_left] at h
  rw [h, (lin_comp R d φ φ hφ hφ).2.1, Matrix.transpose_one, Matrix.one_mul]

variable {O : Type} [CommRing O] [StarRing O]

theorem ax_ad (B : FB R d O) (a : O) : AxOne (B.ad a) := ⟨B.adjoint_zero_fst a, B.adjoint_zero_snd a⟩
theorem ax_sy (B : FB R d O) : AxOne B.sy := ⟨B.symmetry_zero_fst, B.symmetry_zero_snd⟩

theorem bil_ad_mul (B : FB R d O) (a b : O) : bil (B.ad (a * b)) 1 1 =
    (rho B b).transpose * bil (B.ad a) 1 1 + bil (B.ad b) 1 1 * rho B (star a) := by
  have hb : Z (B.A.act b) := B.A.const b
  have hs : Z (B.A.act (star a)) := B.A.const (star a)
  rw [B.ad_mul, bil_mul_left (axOne_compL (ax_ad B a) hb) (axOne_compR (ax_ad B b) hs),
    bil_compL (ax_ad B a) hb, bil_compR (ax_ad B b) hs]
  rfl

theorem bil_ad_add (B : FB R d O) (a b : O) : bil (B.ad (a + b)) 1 1 = bil (B.ad a) 1 1 + bil (B.ad b) 1 1 := by
  have ha : Z (B.A.act a) := B.A.const a
  have hb : Z (B.A.act b) := B.A.const b
  have hsa : Z (B.A.act (star a)) := B.A.const (star a)
  have hsb : Z (B.A.act (star b)) := B.A.const (star b)
  have e := congrArg (fun g => bil g 1 1) (B.ad_add a b)
  have P1 := axOne_xxz (ax3_ph1 B) ha hb
  have P2 := axOne_xzz (ax3_ph2 B) hsa hsb
  rw [bil_mul_left P1 (ax_ad B _), bil_mul_left (axOne_mul (ax_ad B a) (ax_ad B b)) P2,
    bil_mul_left (ax_ad B a) (ax_ad B b),
    bilinear_part_ax3 (ax3_ph1 B) (zero_constant_triple (Z_comp1 ha (Z_pt (n := 2) 0)) (Z_comp1 hb (Z_pt (n := 2) 0)) (Z_pt 1)),
    bilinear_part_ax3 (ax3_ph2 B) (zero_constant_triple (Z_pt (n := 2) 0) (Z_comp1 hsa (Z_pt (n := 2) 1)) (Z_comp1 hsb (Z_pt (n := 2) 1)))] at e
  simpa using e

theorem bil_sy_skew (B : FB R d O) : (bil B.sy 1 1).transpose = - bil B.sy 1 1 := by
  have e := congrArg (fun g => bil g 1 1) B.sy_inv
  rw [bil_mul_left (ax_sy B) (axOne_swap (ax_sy B)), bil_swap] at e
  have h0 : bil (1 : PS R 2 d) 1 1 = 0 := by
    ext i j
    simp [bil, coeff_one]
  rw [h0] at e
  exact eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact e)

theorem bil_ad_sy (B : FB R d O) (a : O) : bil (B.ad a) 1 1 + (bil (B.ad (star a)) 1 1).transpose +
    (rho B a).transpose * bil B.sy 1 1 = bil B.sy 1 1 * rho B (star a) := by
  have ha : Z (B.A.act a) := B.A.const a
  have hs : Z (B.A.act (star a)) := B.A.const (star a)
  have e := congrArg (fun g => bil g 1 1) (B.ad_sy a)
  rw [bil_mul_left (axOne_mul (ax_ad B a) (axOne_swap (ax_ad B _))) (axOne_compL (ax_sy B) ha),
    bil_mul_left (ax_ad B a) (axOne_swap (ax_ad B _)), bil_swap,
    bil_compL (ax_sy B) ha, bil_compR (ax_sy B) hs] at e
  exact e

theorem rhoH_mul (B : FB R d O) (a b : O) : rhoH B (a * b) = rhoH B a * rhoH B b := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  refine Prod.ext ?_ ?_
  · simp [rhoH, rho_mul, Matrix.mulVec_mulVec]
  · simp [rhoH, rho_mul, star_mul, bil_ad_mul, Matrix.transpose_mul, Matrix.add_mulVec,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.transpose_add]
    abel

theorem rhoH_add (B : FB R d O) (a b : O) : rhoH B (a + b) = rhoH B a + rhoH B b := by
  apply LinearMap.ext
  rintro ⟨u, v⟩
  refine Prod.ext ?_ ?_
  · simp [rhoH, rho_add, Matrix.add_mulVec]
  · simp [rhoH, rho_add, star_add, bil_ad_add, Matrix.transpose_add, Matrix.add_mulVec]
    abel

theorem dot_mv (M : Matrix (Fin d) (Fin d) R) (u v : Fin d → R) : M.mulVec u ⬝ᵥ v = u ⬝ᵥ M.transpose.mulVec v := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem pairH_adj (B : FB R d O) (a : O) (y y' : (Fin d → R) × (Fin d → R)) :
    pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') := by
  obtain ⟨u, v⟩ := y
  obtain ⟨u', v'⟩ := y'
  have k := congrArg (fun M => u ⬝ᵥ M.mulVec u') (bil_ad_sy B a)
  simp only [Matrix.add_mulVec, dotProduct_add] at k
  rw [dotProduct_comm u ((bil (B.ad (star a)) 1 1).transpose.mulVec u')] at k
  simp [pairH, rhoH, star_star, Matrix.sub_mulVec, Matrix.mulVec_sub]
  rw [dotProduct_comm v', dotProduct_comm ((rho B a).transpose.mulVec v') u,
    dot_mv (rho B (star a)).transpose, dot_mv (bil (B.ad a) 1 1).transpose,
    dot_mv (rho B a) u ((bil B.sy 1 1).mulVec u'), Matrix.mulVec_mulVec,
    dot_mv (rho B a) u v']
  simp only [Matrix.transpose_transpose]
  linear_combination k

theorem rhoH_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') := by
  intro R _ d O _ _ B
  have r1 : rho B 1 = 1 := by
    show lin (B.A.act 1) 1 = 1
    rw [B.A.one_act]
    exact (lin_comp R d (pt R d 0) (pt R d 0) (Z_pt 0) (Z_pt 0)).2.1
  have b1 : bil (B.ad 1) 1 1 = 0 := by
    rw [B.ad_one]
    ext i j
    simp [bil, coeff_one]
  have one : rhoH B 1 = 1 := by
    apply LinearMap.ext
    rintro ⟨u, v⟩
    simp [rhoH, r1, b1]
  have zero : rhoH B 0 = 0 := by
    have h := rhoH_add B 0 0
    simpa using h
  let f : O →+* Module.End R ((Fin d → R) × (Fin d → R)) :=
    { toFun := rhoH B, map_one' := one, map_mul' := fun a b => rhoH_mul B a b,
      map_zero' := zero, map_add' := fun a b => rhoH_add B a b }
  exact ⟨⟨f, fun a => rfl⟩, bil_sy_skew B, fun a y y' => pairH_adj B a y y'⟩

private theorem lin_mul_lin_eq_one_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam) :
    lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 := by
  have e := (lin_comp R d φ φ h.c₁ h.c₁).2.1
  constructor
  · rw [← lin_comp1 φ h.c₂, h.inv₁, e]
  · rw [← lin_comp1 ψ h.c₁, h.inv₂, e]

private theorem rho_mul_lin_eq_lin_mul_rho_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam) (a : O) :
    rho B a * lin φ 1 = lin φ 1 * rho B₂ a := by
  have e := congrArg (fun g => lin g 1) (h.act a)
  rw [lin_comp1 φ (B₂.A.const a), lin_comp1 _ h.c₁] at e
  exact e.symm

private theorem bil_ad_add_bil_mul_rho_star_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam) (a : O) :
    bil (B₂.ad a) 1 1 + bil lam 1 1 * rho B₂ (star a) =
      (rho B₂ a).transpose * bil lam 1 1 + (lin φ 1).transpose * bil (B.ad a) 1 1 * lin φ 1 := by
  have ha : Z (B₂.A.act a) := B₂.A.const a
  have hs : Z (B₂.A.act (star a)) := B₂.A.const (star a)
  have e := congrArg (fun g => bil g 1 1) (h.ad a)
  rw [bil_mul_left (ax_ad B₂ a) (axOne_compR h.ax hs), bil_compR h.ax hs,
    bil_mul_left (axOne_compL h.ax ha) (axOne_comp (ax_ad B a) h.c₁ h.c₁), bil_compL h.ax ha,
    bil_comp (ax_ad B a) h.c₁ h.c₁] at e
  exact e

private theorem bil_sy_add_bil_eq_of_isIso {B B₂ : FB R d O} {φ ψ : Pt R 1 d} {lam : PS R 2 d} (h : IsIso B B₂ φ ψ lam) :
    bil B₂.sy 1 1 + bil lam 1 1 = (lin φ 1).transpose * bil B.sy 1 1 * lin φ 1 + (bil lam 1 1).transpose := by
  have e := congrArg (fun g => bil g 1 1) h.sy
  rw [bil_mul_left (ax_sy B₂) h.ax, bil_mul_left (axOne_comp (ax_sy B) h.c₁ h.c₁) (axOne_swap h.ax),
    bil_comp (ax_sy B) h.c₁ h.c₁, bil_swap] at e
  exact e

theorem iso_rho : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' := by
  intro R _ d O _ _ B B₂ φ ψ lam h
  obtain ⟨i1, i2⟩ := lin_mul_lin_eq_one_of_isIso h
  have c := rho_mul_lin_eq_lin_mul_rho_of_isIso h
  have t1 : (lin ψ 1).transpose * (lin φ 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, i1, Matrix.transpose_one]
  have t2 : (lin φ 1).transpose * (lin ψ 1).transpose = 1 := by
    rw [← Matrix.transpose_mul, i2, Matrix.transpose_one]
  refine ⟨i1, i2, ?_, c, ?_, ?_⟩
  · rw [Function.bijective_iff_has_inverse]
    refine ⟨fun y => ((lin ψ 1).mulVec y.1,
      (lin φ 1).transpose.mulVec y.2 - (bil lam 1 1).transpose.mulVec ((lin ψ 1).mulVec y.1)), ?_, ?_⟩
    · rintro ⟨u, v⟩
      simp [transH, Matrix.mulVec_mulVec, Matrix.mulVec_add, i2, ← Matrix.mul_assoc, t2]
    · rintro ⟨u, v⟩
      simp [transH, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_add, i1, t1]
  · intro a
    have k1 : lin ψ 1 * rho B (star a) = rho B₂ (star a) * lin ψ 1 := by
      calc lin ψ 1 * rho B (star a) = lin ψ 1 * rho B (star a) * (lin φ 1 * lin ψ 1) := by
            rw [i1, mul_one]
        _ = lin ψ 1 * (rho B (star a) * lin φ 1) * lin ψ 1 := by noncomm_ring
        _ = lin ψ 1 * (lin φ 1 * rho B₂ (star a)) * lin ψ 1 := by rw [c]
        _ = (lin ψ 1 * lin φ 1) * rho B₂ (star a) * lin ψ 1 := by noncomm_ring
        _ = rho B₂ (star a) * lin ψ 1 := by rw [i2, one_mul]
    have r3 := bil_ad_add_bil_mul_rho_star_of_isIso h a
    have k2 : bil lam 1 1 * lin ψ 1 * rho B (star a) =
        (rho B₂ a).transpose * bil lam 1 1 * lin ψ 1 - bil (B₂.ad a) 1 1 * lin ψ 1 +
          (lin φ 1).transpose * bil (B.ad a) 1 1 := by
      calc bil lam 1 1 * lin ψ 1 * rho B (star a)
            = bil lam 1 1 * (rho B₂ (star a) * lin ψ 1) := by rw [mul_assoc, k1]
        _ = (bil (B₂.ad a) 1 1 + bil lam 1 1 * rho B₂ (star a)) * lin ψ 1 - bil (B₂.ad a) 1 1 * lin ψ 1 := by
            noncomm_ring
        _ = ((rho B₂ a).transpose * bil lam 1 1 + (lin φ 1).transpose * bil (B.ad a) 1 1 * lin φ 1) * lin ψ 1
              - bil (B₂.ad a) 1 1 * lin ψ 1 := by rw [r3]
        _ = _ := by
            rw [add_mul, mul_assoc ((lin φ 1).transpose * bil (B.ad a) 1 1) (lin φ 1) (lin ψ 1), i1, mul_one]
            abel
    have m1 := congrArg Matrix.transpose k1
    have m2 := congrArg Matrix.transpose k2
    simp only [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_transpose] at m1 m2
    apply LinearMap.ext
    rintro ⟨u, v⟩
    refine Prod.ext ?_ ?_
    · simp [rhoH, transH, Matrix.mulVec_mulVec, c a]
    · simp [rhoH, transH, Matrix.mulVec_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub]
      rw [m1, m2]
      simp [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mul_assoc]
      abel
  · rintro ⟨u, v⟩ ⟨u', v'⟩
    have k := congrArg (fun M => u ⬝ᵥ M.mulVec u') (bil_sy_add_bil_eq_of_isIso h)
    simp only [Matrix.add_mulVec, dotProduct_add, Matrix.mul_assoc] at k
    rw [dotProduct_comm u ((bil lam 1 1).transpose.mulVec u'), dot_mv (bil lam 1 1).transpose u' u,
      Matrix.transpose_transpose] at k
    simp [pairH, transH, Matrix.mulVec_add]
    rw [dot_mv (lin ψ 1).transpose v', dot_mv ((lin ψ 1).transpose * (bil lam 1 1).transpose) u',
      dot_mv (lin ψ 1).transpose v, dot_mv ((lin ψ 1).transpose * (bil lam 1 1).transpose) u,
      dot_mv (lin φ 1) u]
    simp only [Matrix.transpose_transpose, Matrix.transpose_mul, Matrix.mulVec_mulVec, Matrix.mul_assoc, i2,
      Matrix.mul_one, Matrix.one_mulVec]
    linear_combination (-1 : R) * k

end PositivityTheory.HtPt.Ca
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransport
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj.Iso

theorem rho_pairing : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' :=
  PositivityTheory.HtPt.Ca.iso_rho

end GlobalTheory.CompanionTheory.Ar.Conj.Iso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_isomorphism_transport : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (B₂ : FB R d O) (φ ψ : Pt R 1 d) (lam : PS R 2 d), IsIso B B₂ φ ψ lam → lin φ 1 * lin ψ 1 = 1 ∧ lin ψ 1 * lin φ 1 = 1 ∧ Function.Bijective (transH φ ψ lam) ∧ (∀ a, rho B a * lin φ 1 = lin φ 1 * rho B₂ a) ∧ (∀ a, rhoH B a ∘ₗ transH φ ψ lam = transH φ ψ lam ∘ₗ rhoH B₂ a) ∧ ∀ y y', pairH B (transH φ ψ lam y) (transH φ ψ lam y') = pairH B₂ y y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing | exact GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Iso.rho_pairing <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairing
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.Conj

theorem rhoH_hom_adjoint : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') :=
  @PositivityTheory.HtPt.Ca.rhoH_hom

end GlobalTheory.CompanionTheory.Ar.Conj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalHermitianActionPairingStatement
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_hermitian_action_pairing : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∃ ρH : O →+* Module.End R ((Fin d → R) × (Fin d → R)), ∀ a, ρH a = rhoH B a) ∧ (bil B.sy 1 1).transpose = - bil B.sy 1 1 ∧ ∀ a y y', pairH B (rhoH B a y) y' = pairH B y (rhoH B (star a) y') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint | exact GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rhoH_hom_adjoint <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDuality
section -- merged from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.HFundinv
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace PositivityTheory.UnitarySelfGeneration

private theorem sum_shift_mul_neg_indicator_eq_ite (N : ℕ) (m n : Fin N) :
    ∑ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = if n = m then 1 else 0 := by
  have e1 : ∀ k : Fin N, (((if (k:ℕ) + 1 = (m:ℕ) then (1:ℤ) else 0) - if k = m then 1 else 0) * (if n ≤ k then -1 else 0))
      = (if k = m then (if n ≤ k then (1:ℤ) else 0) else 0) - (if (k:ℕ) + 1 = m then (if n ≤ k then (1:ℤ) else 0) else 0) := by
    intro k
    by_cases h1 : (k:ℕ) + 1 = m
    · have : k ≠ m := by intro h; subst h; omega
      split_ifs <;> simp_all
    · split_ifs <;> simp_all
  simp only [e1, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rcases m with ⟨m, hm⟩
  rcases n with ⟨n, hn⟩
  cases m with
  | zero =>
    have : ∀ k : Fin N, ¬ ((k:ℕ) + 1 = 0) := fun k => by omega
    simp only [this, if_false, Finset.sum_const_zero, sub_zero, Fin.le_def, Fin.mk.injEq]
    split_ifs <;> omega
  | succ m =>
    rw [Finset.sum_eq_single ⟨m, by omega⟩]
    · simp only [Fin.le_def, Fin.mk.injEq]
      split_ifs <;> omega
    · intro b _ hb
      have hb' : (b:ℕ) ≠ m := fun h => hb (Fin.ext h)
      have : ¬ ((b:ℕ) + 1 = ((⟨m + 1, hm⟩ : Fin N) : ℕ)) := by simp only [Fin.val_mk]; omega
      rw [if_neg this]
    · simp

theorem h_fundinv : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  intro Ψ _ _ N r r'
  refine ⟨?_, fun π => ?_⟩
  · obtain ⟨p, m⟩ := r
    obtain ⟨q, n⟩ := r'
    rw [Fintype.sum_prod_type]
    simp only [rootOnFund, fundOnRoot]
    rw [Finset.sum_eq_single p (fun b _ hb => by simp [hb]) (by simp)]
    by_cases hq : q = p
    · subst hq
      simp only [if_true, true_and, Prod.mk.injEq]
      rw [sum_shift_mul_neg_indicator_eq_ite N m n]
      by_cases h : n = m
      · simp [h]
      · simp [h, Ne.symm h]
    · have : ¬ (p = q) := fun h => hq h.symm
      simp [hq, this]
  · simp [rootOnFund, fundOnRoot, π.injective.eq_iff]

end PositivityTheory.UnitarySelfGeneration
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDuality
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOnFund_mul_fundOnRoot_inverse : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') :=
  @PositivityTheory.UnitarySelfGeneration.h_fundinv

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RootFundamentalWeightDualityStatement
open MvPolynomial AlgebraicGeometry CategoryTheory NumberField Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (IsPullHerm imageZ blockFnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_fundamental_weight_duality : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (r r' : Ψ × Fin N), (∑ a, rootOnFund r a * fundOnRoot a r' = if r = r' then 1 else 0) ∧ (∀ π : Ψ ≃ Ψ, rootOnFund (π r.1, r.2) (π r'.1, r'.2) = rootOnFund r r' ∧ fundOnRoot (π r.1, r.2) (π r'.1, r'.2) = fundOnRoot r r') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse | exact GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.rootOnFund_mul_fundOnRoot_inverse <;> assumption)
end
end
