module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PInvMin
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem aeval_inv_reverse_eq_zero_iff {K A : Type} [Field K] [Ring A] [Algebra K A] (u : Aˣ) (f : K[X]) :
    Polynomial.aeval (↑u⁻¹ : A) f.reverse = 0 ↔ Polynomial.aeval (u : A) f = 0 := by
  let S : Subalgebra K A := Algebra.adjoin K {(u : A), ↑u⁻¹}
  letI : IsMulCommutative S := Algebra.isMulCommutative_adjoin K (by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp)
  letI : CommRing S := { mul_comm := isMulCommutative_iff.mp inferInstance }
  let x : S := ⟨u, Algebra.subset_adjoin (by simp)⟩
  let y : S := ⟨↑u⁻¹, Algebra.subset_adjoin (by simp)⟩
  letI : Invertible x := ⟨y, Subtype.ext (by simp [x, y]), Subtype.ext (by simp [x, y])⟩
  have key := Polynomial.eval₂_reverse_eq_zero_iff (algebraMap K S) x f
  have h1 : Polynomial.aeval (↑u⁻¹ : A) f.reverse = S.val (Polynomial.aeval y f.reverse) :=
    Polynomial.aeval_algHom_apply S.val y f.reverse
  have h2 : Polynomial.aeval (u : A) f = S.val (Polynomial.aeval x f) :=
    Polynomial.aeval_algHom_apply S.val x f
  rw [h1, h2, map_eq_zero_iff S.val Subtype.val_injective, map_eq_zero_iff S.val Subtype.val_injective,
    Polynomial.aeval_def, Polynomial.aeval_def]
  exact key

private theorem squarefree_mirror {F : Type} [Field F] (f : F[X]) (h : Squarefree f) :
    Squarefree f.mirror := by
  intro r hr
  obtain ⟨s, hs⟩ := hr
  have hf : f = r.mirror * r.mirror * s.mirror := by
    rw [← Polynomial.mirror_mul_of_domain, ← Polynomial.mirror_mul_of_domain, ← hs,
      Polynomial.mirror_mirror]
  have hu : IsUnit r.mirror := h _ ⟨_, hf⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [Polynomial.mirror_zero] at hu
    exact not_isUnit_zero hu
  rw [Polynomial.isUnit_iff_degree_eq_zero] at hu ⊢
  rw [Polynomial.degree_eq_natDegree hr0]
  rw [Polynomial.degree_eq_natDegree (Polynomial.mirror_eq_zero.not.mpr hr0),
    Polynomial.mirror_natDegree] at hu
  exact hu

private theorem separable_reverse_of_coeff_zero_ne_zero {K : Type} [Field K] (f : K[X]) (h0 : f.coeff 0 ≠ 0)
    (hs : f.Separable) : f.reverse.Separable := by
  rw [← Polynomial.separable_map (algebraMap K (AlgebraicClosure K))]
  have hm : (f.reverse).map (algebraMap K (AlgebraicClosure K)) =
      (f.map (algebraMap K (AlgebraicClosure K))).mirror := by
    have htd : (f.map (algebraMap K (AlgebraicClosure K))).natTrailingDegree = 0 :=
      Polynomial.natTrailingDegree_eq_zero.mpr
        (Or.inr (by rw [Polynomial.coeff_map]; exact (_root_.map_ne_zero _).mpr h0))
    rw [Polynomial.mirror, htd, pow_zero, _root_.mul_one]
    simp only [Polynomial.reverse, Polynomial.natDegree_map, Polynomial.reflect_map]
  rw [hm, PerfectField.separable_iff_squarefree]
  exact squarefree_mirror _ ((Polynomial.separable_map _).mpr hs).squarefree

theorem UpperTheory.Gal.W2.invMin_of :
    UpperTheory.Gal.W2.InvMin := by
  intro K A _ _ _ _ _ u
  have hint : ∀ v : Aˣ, IsIntegral K (v : A) := fun v => .of_finite K _
  have hc : ∀ v : Aˣ, (minpoly K (v : A)).coeff 0 ≠ 0 := by
    intro v h0
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hne := minpoly.ne_zero (hint v)
    have hq0 : q ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hq
      exact hne hq
    have hev : Polynomial.aeval (v : A) q = 0 := by
      have := minpoly.aeval K (v : A)
      rw [hq, map_mul, Polynomial.aeval_X] at this
      simpa using congrArg (fun z => (↑v⁻¹ : A) * z) this
    have hdeg := minpoly.degree_le_of_ne_zero K (v : A) hq0 hev
    have h2 := Polynomial.natDegree_le_natDegree hdeg
    rw [hq, Polynomial.natDegree_X_mul hq0] at h2
    omega
  set p := minpoly K (u : A) with hp
  have htd : p.natTrailingDegree = 0 := Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr (hc u))
  have hdegrev : p.reverse.natDegree = p.natDegree := by
    rw [Polynomial.reverse_natDegree, htd, Nat.sub_zero]
  have hinvMonic : (invPoly p).Monic := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.reverse_leadingCoeff,
      Polynomial.trailingCoeff_eq_coeff_zero (hc u), inv_mul_cancel₀ (hc u)]
  have hinvDeg : (invPoly p).natDegree = p.natDegree := by
    show (Polynomial.C (p.coeff 0)⁻¹ * p.reverse).natDegree = _
    rw [Polynomial.natDegree_C_mul (inv_ne_zero (hc u)), hdegrev]
  have hinvEval : Polynomial.aeval (↑u⁻¹ : A) (invPoly p) = 0 := by
    show Polynomial.aeval (↑u⁻¹ : A) (Polynomial.C (p.coeff 0)⁻¹ * p.reverse) = 0
    rw [map_mul, (aeval_inv_reverse_eq_zero_iff u p).mpr (minpoly.aeval K _), mul_zero]
  have heq : minpoly K (↑u⁻¹ : A) = invPoly p := by
    refine (minpoly.unique K _ hinvMonic hinvEval ?_).symm
    intro q hqm hqe
    have hq0 : q ≠ 0 := hqm.ne_zero
    have h1 : Polynomial.aeval (u : A) q.reverse = 0 := by
      have := (aeval_inv_reverse_eq_zero_iff u⁻¹ q).mpr hqe
      simpa using this
    have h2 := minpoly.degree_le_of_ne_zero K (u : A) (mt Polynomial.reverse_eq_zero.mp hq0) h1
    have h3 := Polynomial.natDegree_le_natDegree h2
    have h4 := Polynomial.reverse_natDegree_le q
    rw [Polynomial.degree_eq_natDegree hinvMonic.ne_zero, Polynomial.degree_eq_natDegree hq0, hinvDeg]
    exact_mod_cast h3.trans h4
  refine ⟨heq, by rw [heq, hinvDeg], fun hs => ?_⟩
  rw [heq]
  have hrev : p.reverse.Separable := separable_reverse_of_coeff_zero_ne_zero p (hc u) hs
  refine hrev.of_dvd ⟨Polynomial.C (p.coeff 0), ?_⟩
  show p.reverse = Polynomial.C (p.coeff 0)⁻¹ * p.reverse * Polynomial.C (p.coeff 0)
  rw [_root_.mul_comm, ← _root_.mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ (hc u),
    Polynomial.C_1, _root_.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.ActComm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2.PActY

variable {p : ℕ} [Fact p.Prime]

private theorem sh_sh' (G : HTGroup p) (a : G.C) : sh G (sh G a) = a := G.star_star a

private theorem key (G : HTGroup p) (β y : G.Cˣ) (s : ℚ)
    (h : (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β) :
    sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
  calc sh G y * ((β⁻¹ : G.Cˣ) : G.C) * y
      = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β * sh G y) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        simp only [_root_.mul_assoc, Units.inv_mul_cancel_left]
    _ = ((β⁻¹ : G.Cˣ) : G.C) * ((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C s * β) * ((β⁻¹ : G.Cˣ) : G.C) * y := by
        rw [h]
    _ = algebraMap ℚ G.C s * ((β⁻¹ : G.Cˣ) : G.C) := by
        simp only [_root_.mul_assoc, Units.mul_inv_cancel_left]
        rw [Algebra.commutes s (y : G.C), Units.inv_mul_cancel_left]
        exact (Algebra.commutes s _).symm

private theorem form_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (u w : VQ D) : formB L β (actY L y u) (actY L y w) = (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) * formB L β u w := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.2.1
  have h1 := L.adj (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
    (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) w
  rw [sh_sh'] at h1
  have h2 : L.rep (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))
      (L.rep ((β⁻¹ : G.Cˣ) : G.C) (L.rep (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) u)) =
      (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) • L.rep ((β⁻¹ : G.Cˣ) : G.C) u := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk, map_mul,
      AlgHom.commutes, Module.End.mul_apply, Module.algebraMap_end_apply]
  simp only [formB, actY]
  rw [← h1, h2, map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem act_comm {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (c : D.O) (w : VQ D) : actY L y (actQ D c w) = actQ D c (actY L y w) := by
  have h := (L.rep_range (actY L y)).1 ⟨_, rfl⟩ c
  exact LinearMap.congr_fun h w

private theorem act_inv {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (w : VQ D) : actY L y (L.rep (((((y : G.Cˣ × ℚˣ).1 : G.Cˣ))⁻¹ : G.Cˣ) : G.C) w) = w := by
  simp only [actY]
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

private theorem per_act {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (Q Q' : VQ D →+ (Fin D.g → ℂ)) (hP : IsPerQ L β ρ Q)
    (hQ : ∀ w, Q' (actY L y w) = Q w) : IsPerQ L β ρ Q' := by
  obtain ⟨h1, h2, Hm, hH, hpos, him⟩ := hP
  have hsc : ∀ (c : ℂ) (z z' : Fin D.g → ℂ), hermForm (c • Hm) z z' = c * hermForm Hm z z' := by
    intro c z z'
    simp only [hermForm, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hQ' : ∀ u, Q' u = Q (L.rep ((((y : G.Cˣ × ℚˣ).1 : G.Cˣ)⁻¹ : G.Cˣ) : G.C) u) := by
    intro u
    rw [← hQ, act_inv]
  refine ⟨fun c w => ?_, ?_, (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • Hm, ?_, fun z hz => ?_, fun u w => ?_⟩
  · rw [hQ', hQ', ← h1]
    congr 1
    exact LinearMap.congr_fun ((L.rep_range _).1 ⟨_, rfl⟩ c) w
  · rw [eq_top_iff, ← h2]
    apply Submodule.span_mono
    rintro _ ⟨w, rfl⟩
    exact ⟨_, hQ w⟩
  · simp [Matrix.IsHermitian, Matrix.conjTranspose_smul, hH.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [hsc, Complex.re_ofReal_mul]
    exact mul_pos hr (hpos z hz)
  · rw [← act_inv L β y u, ← act_inv L β y w, hQ, hQ, hsc, form_act, Complex.im_ofReal_mul, him]
    push_cast
    ring

private theorem psi_rat (G : HTGroup p) (v : InfinitePlace G.F) (s : ℚ) :
    G.psi v (algebraMap ℚ G.C s) = ((s : ℝ) : ℂ) • (1 : Matrix (Fin G.n) (Fin G.n) ℂ) := by
  have he : v.embedding (algebraMap ℚ G.F s) = (s : ℂ) := map_ratCast (v.embedding.comp (algebraMap ℚ G.F)) s
  rw [IsScalarTower.algebraMap_apply ℚ G.F G.C, G.psi_F, he]
  ext i j
  simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

private theorem pos_act (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : GlobalTheory.LKCx.grp G β)
    (z : GlobalTheory.LKCx.PosV G v β) :
    0 < (star ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1) ⬝ᵥ
      (GlobalTheory.LKCx.herm G v β *ᵥ ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1))).re := by
  have hk := key G β (y : G.Cˣ × ℚˣ).1 (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) y.prop.1
  have hr : (0 : ℝ) < ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
    exact_mod_cast y.prop.2
  have hV : ((GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ)) =
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) := rfl
  have hg : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * G.gram v =
      G.gram v * G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) := by
    rw [show sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      MulOpposite.unop (G.star (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) from rfl, G.psi_star,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (G.gram_det v)), Matrix.one_mul]
  have hpsi : G.psi v (sh G (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) * G.psi v ((β⁻¹ : G.Cˣ) : G.C) *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • G.psi v ((β⁻¹ : G.Cˣ) : G.C) := by
    rw [← map_mul, ← map_mul, hk, map_mul, psi_rat, smul_one_mul]
  have hM : (G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C))ᴴ * GlobalTheory.LKCx.herm G v β *
      G.psi v (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) =
      (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) : ℂ) • GlobalTheory.LKCx.herm G v β := by
    simp only [GlobalTheory.LKCx.herm]
    rw [← Matrix.mul_assoc, hg, ← Matrix.mul_smul, ← hpsi]
    simp only [Matrix.mul_assoc]
  rw [hV, Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, hM, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  exact mul_pos hr z.2

end UpperTheory.Gal.W2.PActY

open UpperTheory.Gal.W2.PActY in
theorem UpperTheory.Gal.W2.actY_of :
    UpperTheory.Gal.W2.ActY := by
  intro p _ D G L β y
  exact ⟨form_act L β y, act_comm L β y, fun ρ Q Q' hP hQ => per_act L β y ρ Q Q' hP hQ,
    fun v z _ => ⟨⟨_, pos_act G v β y z⟩, rfl⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PSumPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem finsum_sigma {I : Type} {κ : I → Type} (f : (Σ i, κ i) → ℂ)
    (hf : (Function.support f).Finite) : ∑ᶠ s, f s = ∑ᶠ i, ∑ᶠ k, f ⟨i, k⟩ := by
  classical
  have hfi : ∀ i, (Function.support (fun k : κ i => f ⟨i, k⟩)).Finite := fun i =>
    hf.preimage (fun a _ b _ h => sigma_mk_injective h)
  rw [finsum_eq_sum_of_support_subset f (s := hf.toFinset) (by simp)]
  have hg : Function.support (fun i => ∑ᶠ k, f ⟨i, k⟩) ⊆ ↑(hf.toFinset.image Sigma.fst) := by
    intro i hi
    obtain ⟨k, hk⟩ : ∃ k, f ⟨i, k⟩ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hi (finsum_eq_zero_of_forall_eq_zero h)
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
    exact ⟨⟨i, k⟩, by simpa using hk, rfl⟩
  rw [finsum_eq_sum_of_support_subset _ hg]
  have hk : ∀ i, ∑ᶠ k, f ⟨i, k⟩ = ∑ k ∈ (hfi i).toFinset, f ⟨i, k⟩ := fun i =>
    finsum_eq_sum_of_support_subset _ (by simp)
  simp_rw [hk]
  rw [← Finset.sum_sigma]
  apply Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ⟨i, k⟩
  simp only [Set.Finite.mem_toFinset, Function.mem_support, Finset.mem_sigma, Finset.mem_image]
  constructor
  · intro h
    exact ⟨⟨⟨i, k⟩, h, rfl⟩, h⟩
  · rintro ⟨-, h⟩
    exact h

private noncomputable def tm {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β) : ℂ :=
  ((Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) : ℕ) : ℂ)⁻¹ *
    ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if GlobalTheory.LKCx.FixL G v B.β y b.2.1 then
      (S.indicator (1 : G.GAf → ℂ)) (b.1.1⁻¹ * B.toAf y * b.1.1) *
        (((KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator (1 : Gr G 1 → ℂ))
          (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2) *
        c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0

private theorem tm_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} (v : InfinitePlace G.F) (c : G.F[X] → ℂ → ℂ)
    (K : Subgroup G.GAf) (S : Set G.GAf) (B : GlobalTheory.LKCx.Form G) (b : GlobalTheory.LKCx.Dat G v B.β)
    (hK : ∀ y, Sees B (K : Set G.GAf) b y → y = 1) :
    tm v c K S B b = ∑ᶠ y : GlobalTheory.LKCx.grp G B.β, if Sees B S b y then
      c (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) (GlobalTheory.RootSumWeights.eigL G v B.β y b.2.1) else 0 := by
  have hcard : Nat.card (GlobalTheory.LKCx.Form.Stab v B K (KHT p G.m G.n 1 G.Fw) b) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun s t => ?_⟩, ⟨LKCx.Stab.one G v B.β _ _ _ K _ b⟩⟩
    obtain ⟨y, hy1, hy2, hy3⟩ := s
    obtain ⟨y', hy1', hy2', hy3'⟩ := t
    have e1 : y = 1 := hK y ⟨hy3, hy1, hy2⟩
    have e2 : y' = 1 := hK y' ⟨hy3', hy1', hy2'⟩
    subst e1
    subst e2
    rfl
  unfold tm
  rw [hcard, Nat.cast_one, inv_one, _root_.one_mul]
  apply finsum_congr
  intro y
  unfold Sees
  by_cases hF : GlobalTheory.LKCx.FixL G v B.β y b.2.1
  · by_cases h1 : b.1.1⁻¹ * B.toAf y * b.1.1 ∈ S
    · by_cases h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * b.1.2 ∈ KHT p G.m G.n 1 G.Fw
      · simp [hF, h1, h2]
      · simp [hF, h1, h2]
    · simp [hF, h1]
  · simp [hF]

theorem UpperTheory.Gal.W2.sumPts_of :
    UpperTheory.Gal.W2.EigSame → UpperTheory.Gal.W2.SumPts := by
  intro hE p _ G v c K S hconj hK hS T Φ Fb w hx
  classical
  let g : LKCx.AllPts G v K (KHT p G.m G.n 1 G.Fw) → ℂ := fun s => tm v c K S (Quot.out s.1) (Quot.out s.2)
  have key : ∀ x : T, g (Φ x) = if x ∈ Fb then w x else 0 := by
    intro x
    obtain ⟨q, a, hΦ, hFb, hw⟩ := hx x
    obtain ⟨pt, hpt⟩ : ∃ pt : LKCx.Form.Pts v (Quot.out q) K (KHT p G.m G.n 1 G.Fw), Quot.mk _ a = pt := ⟨_, rfl⟩
    rw [hpt] at hΦ
    have hmk : Quot.mk _ a = Quot.mk _ (Quot.out pt) := hpt.trans (Quot.out_eq pt).symm
    obtain ⟨E, -, hE1⟩ := hE p G v c (Quot.out q) K S hconj a (Quot.out pt) hmk
    obtain ⟨E', -, hE2⟩ := hE p G v c (Quot.out q) K S hconj (Quot.out pt) a hmk.symm
    have hg : g (Φ x) = g ⟨q, pt⟩ := by rw [hΦ]
    rw [hg]
    show tm v c K S (Quot.out q) (Quot.out pt) = _
    rw [tm_eq v c K S _ _ (hK _ _)]
    by_cases hxF : x ∈ Fb
    · rw [if_pos hxF]
      obtain ⟨y, hy⟩ := hFb.1 hxF
      have hy' := ((hE1 y).1).1 hy
      rw [finsum_eq_single _ (E y)]
      · rw [if_pos hy', ((hE1 y).2 hy).1, ((hE1 y).2 hy).2, hw y hy]
      · intro y' hne
        rw [if_neg]
        intro hs
        exact hne (hS _ _ _ _ hs hy')
    · rw [if_neg hxF]
      apply finsum_eq_zero_of_forall_eq_zero
      intro y'
      rw [if_neg]
      intro hs
      exact hxF (hFb.2 ⟨E' y', ((hE2 y').1).1 hs⟩)
  have hsupp : Function.support (fun x => g (Φ x)) ⊆ ↑Fb := by
    intro x hx0
    by_contra hn
    exact hx0 (by show g (Φ x) = 0; rw [key x, if_neg (show x ∉ Fb from hn)])
  have hfin : (Function.support g).Finite := by
    apply ((Fb.finite_toSet).image Φ).subset
    intro s hs
    refine ⟨Φ.symm s, hsupp ?_, Φ.apply_symm_apply s⟩
    show g (Φ (Φ.symm s)) ≠ 0
    rw [Φ.apply_symm_apply]
    exact hs
  have h1 : RootSumWeights.cxTotalM G v c K (S.indicator 1) (KHT p G.m G.n 1 G.Fw)
      ((↑(KHT p G.m G.n 1 G.Fw) : Set (Gr G 1)).indicator 1) = ∑ᶠ s, g s := by
    rw [finsum_sigma g hfin]
    rfl
  rw [h1, ← finsum_comp_equiv Φ, finsum_eq_sum_of_support_subset (fun x => g (Φ x)) hsupp]
  exact Finset.sum_congr rfl (fun x hx => by rw [key, if_pos hx])
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordKN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)

private theorem smul_mem_laHat {c : AfP p} (hc : IsIntAf c) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    c • v ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  apply KNLevel.mem_laHat_of_repr b
  intro i
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, KNLevel.isIntAf_iff]
  exact mul_mem ((KNLevel.isIntAf_iff _).mp hc)
    ((KNLevel.isIntAf_iff _).mp (KNLevel.repr_isIntAf b v hv i))

private theorem inAf_mem_laHat (a : D.La) : inAf D a ∈ LaHat D := by
  unfold inAf LaHat
  exact AddSubgroup.subset_closure ⟨1, a, (KNLevel.isIntAf_iff 1).mpr (one_mem _), rfl⟩

private theorem exists_den_act (g : G.GAf) :
    ∃ m : ℕ, 0 < m ∧ ∀ z ∈ LaHat D, m • L.actG g z ∈ LaHat D := by
  classical
  haveI := D.freeLa
  haveI := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  let B := KNLevel.bA b
  obtain ⟨m, hm, hden⟩ := AfPCpctDen.exists_den p
    (Set.range fun ki : Module.Free.ChooseBasisIndex ℤ D.La × Module.Free.ChooseBasisIndex ℤ D.La =>
      B.repr (L.actG g (B ki.1)) ki.2) (Set.finite_range _).isCompact
  refine ⟨m, hm, fun z hz => ?_⟩
  have hy : ∀ k, m • L.actG g (B k) ∈ LaHat D := by
    intro k
    apply KNLevel.mem_laHat_of_repr b
    intro i
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul, KNLevel.isIntAf_iff]
    exact hden _ ⟨(k, i), rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← B.sum_repr z, map_sum, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  rw [LinearMap.map_smul, smul_comm m]
  exact smul_mem_laHat (KNLevel.repr_isIntAf b z hz k) (hy k)

private theorem rd_move (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (w : VQ D) :
    rd L x h₂ w = L.actG (h₂⁻¹ * h₁) (rd L x h₁ w) := by
  simp only [rd]
  rw [← Module.End.mul_apply (L.actG (h₂⁻¹ * h₁)), ← map_mul, mul_inv_cancel_right]

private theorem stable (hd : RdDense) (x : (AfP p ⊗[ℚ] G.C)ˣ) (h₁ h₂ : G.GAf) (P : VQ D → Prop)
    (A₁ : ∀ w, P w ↔ rd L x h₁ w ∈ LaHat D) (A₂ : ∀ w, P w ↔ rd L x h₂ w ∈ LaHat D)
    (z : AfP p ⊗[ℚ] VQ D) (hz : z ∈ LaHat D) : L.actG (h₂⁻¹ * h₁) z ∈ LaHat D := by
  obtain ⟨m, hm, hden⟩ := exists_den_act L (h₂⁻¹ * h₁)
  obtain ⟨w, e, he, rfl⟩ := hd p D G L x h₁ m hm z
  have h1 : rd L x h₁ w ∈ LaHat D := by
    have := sub_mem hz (nsmul_mem he m)
    rwa [add_sub_cancel_right] at this
  have h2 : rd L x h₂ w ∈ LaHat D := (A₂ w).mp ((A₁ w).mpr h1)
  rw [map_add (f := _), map_nsmul, ← rd_move L x h₁ h₂ w]
  exact add_mem h2 (hden e he)

private theorem congOne_of_gen {N : ℕ} {g : G.GAf}
    (gen : ∀ a : D.La, ∃ u ∈ LaHat D, L.actG g (inAf D a) = inAf D a + N • u) : L.CongOne N g := by
  unfold Link.CongOne
  intro v hv
  unfold LaHat at hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, y, hc, rfl⟩ := hz
    obtain ⟨u, hu, hgu⟩ := gen y
    have hcy : c ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] y) = c • inAf D y := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    refine ⟨c • u, smul_mem_laHat hc hu, ?_⟩
    rw [hcy, LinearMap.map_smul, hgu, smul_add, smul_comm c N u]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨w₁, hw₁, e₁⟩ := hy
    obtain ⟨w₂, hw₂, e₂⟩ := hz
    exact ⟨w₁ + w₂, add_mem hw₁ hw₂, by rw [map_add (f := _), e₁, e₂, smul_add]; abel⟩
  | neg y _ hy =>
    obtain ⟨w, hw, e⟩ := hy
    exact ⟨-w, neg_mem hw, by rw [map_neg, e, neg_add, smul_neg]⟩

end SlopeTestRemainingChoices

theorem coordKN_of : RdDense → CoordKN := by
  intro hd p _ D G L x N hN hcop D' t j h₁ h₂ hc1
  have memOf : ∀ {g : G.GAf}, L.CongOne N g → ∀ v ∈ LaHat D, L.actG g v ∈ LaHat D := by
    intro g hC v hv
    obtain ⟨w, hw, e⟩ := hC v hv
    rw [e]
    exact add_mem hv (nsmul_mem hw N)
  have cong : ∀ k₁ k₂ : G.GAf, IsCoordA L x N D' t j k₁ → IsCoordA L x N D' t j k₂ →
      L.CongOne N (k₂⁻¹ * k₁) := by
    intro k₁ k₂ hk₁ hk₂
    have hst : ∀ z ∈ LaHat D, L.actG (k₂⁻¹ * k₁) z ∈ LaHat D :=
      stable L hd x k₁ k₂ (fun w => ∃ r u, p ^ r • w = j u) hk₁.1 hk₂.1
    apply congOne_of_gen L
    intro a
    obtain ⟨w₁, hw₁, e₁⟩ := hk₁.2 a
    obtain ⟨w₂, hw₂, e₂⟩ := hk₂.2 a
    refine ⟨w₂ - L.actG (k₂⁻¹ * k₁) w₁, sub_mem hw₂ (hst w₁ hw₁), ?_⟩
    have e₃ := rd_move L x k₁ k₂ (j (t a))
    rw [e₂, e₁, map_add (f := _), map_nsmul] at e₃
    rw [smul_sub, ← add_sub_assoc, e₃]
    abel
  constructor
  · intro hc2
    exact ⟨cong h₁ h₂ hc1 hc2, by rw [mul_inv_rev, inv_inv]; exact cong h₂ h₁ hc2 hc1⟩
  · intro hg
    obtain ⟨hC, hCi⟩ := hg
    have hinv : (h₂⁻¹ * h₁)⁻¹ = h₁⁻¹ * h₂ := by rw [mul_inv_rev, inv_inv]
    refine ⟨fun w => ?_, fun a => ?_⟩
    · rw [hc1.1 w]
      constructor
      · intro hw
        rw [rd_move L x h₁ h₂ w]
        exact memOf hC _ hw
      · intro hw
        rw [rd_move L x h₂ h₁ w, ← hinv]
        exact memOf hCi _ hw
    · obtain ⟨w₁, hw₁, e₁⟩ := hc1.2 a
      obtain ⟨w₃, hw₃, e₃⟩ := hC _ (inAf_mem_laHat a)
      refine ⟨w₃ + L.actG (h₂⁻¹ * h₁) w₁, add_mem hw₃ (memOf hC _ hw₁), ?_⟩
      rw [rd_move L x h₁ h₂, e₁, map_add (f := _), map_nsmul, e₃, smul_add, add_assoc]

end UpperTheory.Gal.W2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PCoordIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem actY_inv_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {β : G.Cˣ}
    (y : GlobalTheory.LKCx.grp G β) (w : VQ D) : actY L y⁻¹ (actY L y w) = w := by
  show L.rep ((y⁻¹ : GlobalTheory.LKCx.grp G β) : G.Cˣ × ℚˣ).1 (L.rep ((y : G.Cˣ × ℚˣ).1 : G.C) w) = w
  rw [← Module.End.mul_apply, ← map_mul]
  simp

private theorem perMove (hA : ActY) {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G)
    {v : InfinitePlace G.F} {t₀ : D.F →+* ℂ} {ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ} {β : G.Cˣ}
    (RD : RDic L v β ρ t₀) (hs : sh G β = β) (y : GlobalTheory.LKCx.grp G β) {Q'' : VQ D →+ (Fin D.g → ℂ)}
    (hQ : IsPerQ L β ρ Q'') (z : GlobalTheory.LKCx.PosV G v β) (hr : RD.rel Q'' z.1) :
    ∃ (Q₁ : VQ D →+ (Fin D.g → ℂ)) (z₁ : GlobalTheory.LKCx.PosV G v β), IsPerQ L β ρ Q₁ ∧
      (∀ w, Q₁ (actY L y w) = Q'' w) ∧ RD.rel Q₁ z₁.1 ∧
      z₁.1 = (GlobalTheory.LKCx.toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z.1 := by
  obtain ⟨-, -, h3, h4⟩ := hA p D G L β y
  let Q₁ : VQ D →+ (Fin D.g → ℂ) := Q''.comp (actY L y⁻¹).toAddMonoidHom
  have e : ∀ w, Q₁ (actY L y w) = Q'' w := fun w => by
    show Q'' (actY L y⁻¹ (actY L y w)) = _
    rw [actY_inv_left]
  obtain ⟨z₁, hz₁⟩ := h4 v z hs
  refine ⟨Q₁, z₁, h3 ρ Q'' Q₁ hQ e, e, ?_, hz₁⟩
  rw [hz₁]
  exact RD.equiv y Q'' Q₁ z.1 e hr

private theorem same_mk {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β) (y : GlobalTheory.LKCx.grp G B.β) (c : ℂ)
    (hc : c ≠ 0) (h1 : b.1.1⁻¹ * B.toAf y * a.1.1 ∈ K) (h2 : b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2 ∈ K')
    (hz : b.2.1 = c • ((GlobalTheory.LKCx.toV G v B.β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a b := by
  refine ⟨y, ((b.1.1⁻¹ * B.toAf y * a.1.1)⁻¹, (b.1.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * a.1.2)⁻¹), c,
    inv_mem h1, inv_mem h2, hc, ?_, hz⟩
  change b.1 = (B.toAf y, GlobalTheory.LKCx.toP1 G B.β y) * a.1 * _
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_mul]
    group
  · simp only [Prod.snd_mul]
    group

private theorem same_of_eq {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} (B : GlobalTheory.LKCx.Form G)
    (K : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : GlobalTheory.LKCx.Dat G v B.β)
    (h : (Quot.mk _ a : GlobalTheory.LKCx.Form.Pts v B K K') = Quot.mk _ b) :
    GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b a := by
  have key : ∀ a b : GlobalTheory.LKCx.Dat G v B.β,
      Relation.EqvGen (GlobalTheory.LKCx.Same G v B.β B.trivAf.choose B.trivAf.choose_spec.choose
        B.trivAf.choose_spec.choose_spec K K') a b →
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b) ∧
      (∃ y : GlobalTheory.LKCx.grp G B.β, y • GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' b =
        GlobalTheory.CxUnfold.OrbitSumGen.pairOfDat G v B.β B.trivAf.choose
          B.trivAf.choose_spec.choose B.trivAf.choose_spec.choose_spec K K' a) := by
    intro a b hab
    induction hab with
    | rel x y hxy =>
      obtain ⟨g, hg⟩ := (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ x y).1 hxy
      exact ⟨⟨g, hg⟩, ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩⟩
    | refl x => exact ⟨⟨1, one_smul _ _⟩, ⟨1, one_smul _ _⟩⟩
    | symm x y _ ih => exact ⟨ih.2, ih.1⟩
    | trans x y z _ _ ih1 ih2 =>
      obtain ⟨⟨g1, hg1⟩, ⟨h1, hh1⟩⟩ := ih1
      obtain ⟨⟨g2, hg2⟩, ⟨h2, hh2⟩⟩ := ih2
      exact ⟨⟨g2 * g1, by rw [mul_smul, hg1, hg2]⟩, ⟨h1 * h2, by rw [mul_smul, hh2, hh1]⟩⟩
  exact (GlobalTheory.CxUnfold.OrbitSumGen.same_iff_smul _ _ _ _ _ _ _ _ b a).2 (key a b (Quot.eqvGen_exact h)).2

end UpperTheory.Gal.W2

private theorem ext_lemma {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {β : G.Cˣ}
    {D' : PLat D.O D.inv} {j : D'.La →+ VQ D} (hj : IsPlace L β D' j) (Q Q₁ : VQ D →+ (Fin D.g → ℂ))
    (h : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)) (hQ : ∀ u, Q (j u) = h (Q₁ (j u))) :
    ∀ w, Q w = h (Q₁ w) := by
  intro w
  obtain ⟨m, u, hm, hmu⟩ := hj.2.2.1 w
  have key : m • Q w = m • h (Q₁ w) := by
    rw [← map_nsmul Q, hmu, hQ, ← hmu, map_nsmul Q₁, map_nsmul h]
  exact smul_right_injective _ hm key

theorem UpperTheory.Gal.W2.coordIso_of :
    UpperTheory.Gal.W2.LatForm → UpperTheory.Gal.W2.LatIso → UpperTheory.Gal.W2.ActY → UpperTheory.Gal.W2.CoordIso := by
  intro hF hI hA p _ D G L v t₀ ρ PD RD N hN hNp D' t P D'' t'' P'' hc hc'' q q'' a a'' j j'' ha ha''
  obtain ⟨hpl, hca, hlp, Q, hQ, hQj, hr⟩ := ha
  obtain ⟨hpl'', hca'', hlp'', Q'', hQ'', hQj'', hr''⟩ := ha''
  constructor
  · rintro ⟨w, h, hw, hPh⟩
    obtain ⟨y, s, hs, hy, hjw⟩ := hF p D G L _ _ D' D'' j j'' hpl hpl'' w.toLinearMap 1 one_pos
      (by intro u u'; rw [_root_.one_mul]; exact hw.1 u u')
    have hjw' : ∀ u, j (w u) = L.rep (y : G.C) (j'' u) := hjw
    have hrel : GlobalTheory.LKCx.Form.Rel (Quot.out q'') (Quot.out q) := by
      refine ⟨y, (s : ℚ)⁻¹, inv_pos.mpr hs, ?_⟩
      rw [hy, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ (ne_of_gt hs), map_one, _root_.one_mul]
    have hq : q'' = q :=
      (Quot.out_eq (q'' : Quot GlobalTheory.LKCx.Form.Rel)).symm.trans
        ((Quot.sound hrel).trans (Quot.out_eq (q : Quot GlobalTheory.LKCx.Form.Rel)))
    subst hq
    let yy : GlobalTheory.LKCx.grp G (Quot.out q'').β := ⟨(y, s), hy, hs⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q'').sym yy hQ'' a''.2 hr''
    have hext : ∃ h' : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ), ∀ w0, Q w0 = h' (Q₁ w0) := by
      refine ⟨h, ext_lemma hpl Q Q₁ h ?_⟩
      intro u
      obtain ⟨u'', rfl⟩ := w.surjective u
      rw [hQj, hPh, ← hQj'', ← hQ₁y, hjw']
      rfl
    obtain ⟨c, hc0, hac⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).1 hext
    have hmem := (hI p D G L (Quot.out q'') (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' yy).2 ⟨w, hw, hjw'⟩
    exact congrArg (Sigma.mk _)
      (Quot.sound (same_mk _ _ _ a'' a yy c hc0 hmem.1 hmem.2 (by rw [hac, hz₁]))).symm
  · intro heq
    obtain ⟨hq, hh⟩ := Sigma.mk.inj heq
    subst hq
    obtain ⟨y, k, c, hk1, hk2, hc0, hk, hz⟩ := same_of_eq _ _ _ a a'' (eq_of_heq hh)
    have hmem1 : a.1.1⁻¹ * (Quot.out q).toAf y * a''.1.1 ∈ L.KN N := by
      have e : a.1.1 = (Quot.out q).toAf y * a''.1.1 * k.1 := congrArg Prod.fst hk
      have e2 : ((Quot.out q).toAf y * a''.1.1 * k.1)⁻¹ * (Quot.out q).toAf y * a''.1.1 = k.1⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk1
    have hmem2 : a.1.2⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 ∈ KHT p G.m G.n 1 G.Fw := by
      have e : a.1.2 = GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2 := congrArg Prod.snd hk
      have e2 : (GlobalTheory.LKCx.toP1 G (Quot.out q).β y * a''.1.2 * k.2)⁻¹ * GlobalTheory.LKCx.toP1 G (Quot.out q).β y *
          a''.1.2 = k.2⁻¹ := by
        group
      rw [e, e2]
      exact inv_mem hk2
    obtain ⟨w, hw, hjw⟩ := (hI p D G L (Quot.out q) (PD _) N hN hNp D' t D'' t'' j j'' a.1 a''.1 N N t t''
      hc hc'' hpl hpl'' hca hca'' hlp hlp'' y).1 ⟨hmem1, hmem2⟩
    obtain ⟨Q₁, z₁, hQ₁, hQ₁y, hr₁, hz₁⟩ := perMove hA L (RD _) (Quot.out q).sym y hQ'' a''.2 hr''
    obtain ⟨h, hh'⟩ := ((RD _).uniq Q₁ Q z₁ a.2 hQ₁ hQ hr₁ hr).2 ⟨c, hc0, by rw [hz, hz₁]⟩
    refine ⟨w, h, hw, fun u => ?_⟩
    rw [← hQj, hjw, hh', hQ₁y, hQj'']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PClsScalar
noncomputable section

open GlobalTheory.PELU GlobalTheory.UPel.HT

namespace UpperTheory.Gal.W2

private lemma power_free {T : Type} (X Y : T → ℤ) (a b : ℕ) (hab : a.Coprime b)
    (h : ∀ t, (b : ℤ) * X t = a * Y t)
    (hP : ∀ q k : ℕ, q.Prime → ((∀ t, ((q ^ k : ℕ) : ℤ) ∣ X t) ↔ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t))
    (t₀ : T) (h0 : Y t₀ ≠ 0) : a = 1 := by
  classical
  by_contra ha
  obtain ⟨q, hq, hqa⟩ := Nat.exists_prime_and_dvd ha
  have hqb : ¬ q ∣ b := fun hqb => hq.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hab hqa hqb)
  have hex : ∃ k, ¬ ∀ t, ((q ^ k : ℕ) : ℤ) ∣ Y t := by
    refine ⟨(Y t₀).natAbs, fun hall => h0 ?_⟩
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hall t₀) ?_
    rw [Int.natAbs_natCast]
    exact Nat.lt_pow_self hq.one_lt
  have hk0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this (fun t => by simp)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hmY : ∀ t, ((q ^ m : ℕ) : ℤ) ∣ Y t := by
    by_contra hc
    exact Nat.find_min hex (by omega) hc
  have hcop : IsCoprime ((q ^ (m + 1) : ℕ) : ℤ) (b : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqb))
  have hX : ∀ t, ((q ^ (m + 1) : ℕ) : ℤ) ∣ X t := by
    intro t
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [h t, pow_succ, Nat.cast_mul, mul_comm (a : ℤ)]
    exact mul_dvd_mul (hmY t) (Int.natCast_dvd_natCast.mpr hqa)
  have := Nat.find_spec hex
  rw [hm] at this
  exact this ((hP q (m + 1) hq).mp hX)

private lemma genus_dvd {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (h : Genus p N D₀ D' t) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (∀ x y, (n : ℤ) ∣ D'.EF x y) ↔ ∀ a a', (n : ℤ) ∣ D₀.EF a a' := by
  obtain ⟨f, ν, -, -, H⟩ := h
  obtain ⟨hν, -, -, honto, hsim⟩ := H n hn hc
  constructor
  · intro hd a a'
    have h1 : (n : ℤ) ∣ ν n * D₀.EF a a' := (dvd_sub_right (hd _ _)).1 (hsim a a')
    exact hν.symm.dvd_of_dvd_mul_left h1
  · intro hd x y
    obtain ⟨a, e, rfl⟩ := honto x
    obtain ⟨a', e', rfl⟩ := honto y
    have h1 : (n : ℤ) ∣ D'.EF (f n a) (f n a') := by
      have h2 := hsim a a'
      have h3 : (n : ℤ) ∣ ν n * D₀.EF a a' := Dvd.dvd.mul_left (hd a a') _
      exact (dvd_sub_left h3).1 h2
    simp only [map_add (f := _), LinearMap.add_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
    exact dvd_add (dvd_add h1 (Dvd.intro _ rfl)) (Dvd.intro _ rfl)

private lemma half_value {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] :
    ∃ (E₁ : LinearMap.BilinForm ℤ D'.La) (e : ℕ) (x y : D'.La), D'.EF = (2 : ℤ) • E₁ ∧ e.Coprime p ∧ E₁ x y = e := by
  obtain ⟨E₁, hE, e, he, hx⟩ := h
  let b := Module.Free.chooseBasis ℤ D'.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨x, hx⟩ := hx (b.coord i)
  refine ⟨E₁, e, x, b i, hE, he, ?_⟩
  rw [hx]
  simp

private lemma half_dvd {O : Type} [Ring O] {bar : O → O} {p : ℕ} {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] (k : ℕ) :
    (∀ x y, ((p ^ k : ℕ) : ℤ) ∣ D'.EF x y) ↔ ((p ^ k : ℕ) : ℤ) ∣ 2 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  constructor
  · intro hall
    have h1 := hall x y
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul] at h1
    have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (e : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left _ he.symm)
    exact hcop.dvd_of_dvd_mul_right h1
  · intro h2 x' y'
    rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul]
    exact dvd_mul_of_dvd_left h2 _

private lemma half_ne {O : Type} [Ring O] {bar : O → O} {p : ℕ} (hp : p.Prime) {D' : PLat O bar}
    (h : HalfPerf p D') [Nontrivial D'.La] : ∃ x y, D'.EF x y ≠ 0 := by
  obtain ⟨E₁, e, x, y, hE, he, hxy⟩ := half_value h
  refine ⟨x, y, ?_⟩
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hp.one_lt.ne' (Nat.coprime_zero_left p |>.mp he)
  rw [hE, LinearMap.smul_apply, LinearMap.smul_apply, hxy, smul_eq_mul]
  exact mul_ne_zero two_ne_zero (by exact_mod_cast he0)

private lemma genus_nontrivial {O : Type} [Ring O] {bar : O → O} {p N : ℕ} {D₀ D' : PLat O bar}
    {t : D₀.La → D'.La} (hp : p.Prime) (h : Genus p N D₀ D' t) [Nontrivial D₀.La] : Nontrivial D'.La := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  obtain ⟨f, ν, -, -, hf⟩ := h
  have hn : 0 < 1 + p := by omega
  have hc : (1 + p).Coprime p := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left p)
  obtain ⟨-, -, hdiv, -, -⟩ := hf (1 + p) hn hc
  let b := Module.Free.chooseBasis ℤ D₀.La
  obtain ⟨i⟩ := b.index_nonempty
  obtain ⟨e, he⟩ := (hdiv (b i)).mp ⟨0, Subsingleton.elim _ _⟩
  have h1 := congrArg (b.coord i) he
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_nsmul,
    Finsupp.smul_apply, nsmul_eq_mul] at h1
  have h2 := Int.eq_one_of_mul_eq_one_right (by positivity) h1.symm
  have := hp.two_le
  omega

theorem clsScalar_of : ClsScalar := by
  intro p _ D N N' D' t D'' t'' hD' hD'' w r hr hEF
  have hp : p.Prime := Fact.out
  haveI : Nontrivial D.plat.La := by
    show Nontrivial D.La
    refine Module.nontrivial_of_finrank_pos (R := ℤ) ?_
    rw [D.rankLa]
    have h1 := D.m_pos
    have h2 := D.n_pos
    have h3 : 0 < Module.finrank ℚ D.F := Module.finrank_pos
    positivity
  haveI : Nontrivial D'.La := genus_nontrivial hp hD'.1
  haveI : Nontrivial D''.La := genus_nontrivial hp hD''.1
  let X : D''.La × D''.La → ℤ := fun u => D'.EF (w u.1) (w u.2)
  let Y : D''.La × D''.La → ℤ := fun u => D''.EF u.1 u.2
  have hXall : ∀ m : ℤ, (∀ u, m ∣ X u) ↔ ∀ x y, m ∣ D'.EF x y := fun m =>
    ⟨fun h x y => by simpa [X] using h (w.symm x, w.symm y), fun h u => h _ _⟩
  have hYall : ∀ m : ℤ, (∀ u, m ∣ Y u) ↔ ∀ x y, m ∣ D''.EF x y := fun m =>
    ⟨fun h x y => h (x, y), fun h u => h _ _⟩
  have hP : ∀ q k : ℕ, q.Prime → ((∀ u, ((q ^ k : ℕ) : ℤ) ∣ X u) ↔ ∀ u, ((q ^ k : ℕ) : ℤ) ∣ Y u) := by
    intro q k hq
    rw [hXall, hYall]
    by_cases hqp : q = p
    · subst hqp
      rw [half_dvd hD'.2, half_dvd hD''.2]
    · have hpos : 0 < q ^ k := pow_pos hq.pos k
      have hcop : (q ^ k).Coprime p := Nat.Coprime.pow_left k ((Nat.coprime_primes hq hp).mpr hqp)
      rw [genus_dvd hD'.1 _ hpos hcop, genus_dvd hD''.1 _ hpos hcop]
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hkey : ∀ u, (r.den : ℤ) * X u = (r.num.natAbs : ℤ) * Y u := by
    intro u
    rw [Int.natAbs_of_nonneg hnum.le]
    have h1 := hEF u.1 u.2
    have h2 : ((r.den : ℤ) * X u : ℚ) = (r.num * Y u : ℚ) := by
      push_cast
      rw [show (X u : ℚ) = ((D'.EF (w u.1) (w u.2) : ℤ) : ℚ) from rfl, h1, ← Rat.mul_den_eq_num]
      ring
    exact_mod_cast h2
  obtain ⟨x₀, y₀, h0⟩ := half_ne hp hD''.2
  obtain ⟨x₁, y₁, h1⟩ := half_ne hp hD'.2
  have ha : r.num.natAbs = 1 :=
    power_free X Y r.num.natAbs r.den r.reduced hkey hP (x₀, y₀) h0
  have hb : r.den = 1 :=
    power_free Y X r.den r.num.natAbs r.reduced.symm (fun u => (hkey u).symm)
      (fun q k hq => (hP q k hq).symm) (w.symm x₁, w.symm y₁) (by simpa [X] using h1)
  have hn1 : r.num = 1 := by omega
  rw [← Rat.num_div_den r, hn1, hb]
  norm_num

end UpperTheory.Gal.W2
end
end
