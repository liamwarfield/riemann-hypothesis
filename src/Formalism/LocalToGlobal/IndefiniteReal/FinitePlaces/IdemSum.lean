module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.TameAtOne

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartPhiE
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Main

variable {D : D7}

theorem finPart_phiE (v : HeightOneSpectrum (𝓞 D.host.F)) (a : v.adicCompletion D.host.F) :
    finPart D (phiE v a) = sglV v a ⊗ₜ[D.host.F] (1 : D.host.E) := by
  simp only [phiE, finPart, Algebra.TensorProduct.algebraMap_apply, RingHom.coe_coe,
    AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  rfl

theorem finPart_incA (w : D.host.E) : finPart D (incA D w) = (1 : Af D.host.F) ⊗ₜ[D.host.F] w := by
  simp only [incA, finPart, RingHom.coe_coe, AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
  rfl

theorem tmul_eq (a : AF D.host.F) (w : D.host.E) :
    a ⊗ₜ[D.host.F] w = algebraMap (AF D.host.F) (AE D) a * incA D w := by
  simp only [incA, Algebra.TensorProduct.algebraMap_apply]
  unfold inclR
  simp [Algebra.TensorProduct.tmul_mul_tmul]


set_option maxHeartbeats 800000 in
theorem mul_e_of (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AE D) (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F)
    (hid : ∀ w : D.host.E, e * incA D w = e * phiE v (ι w)) (heps : e * phiE v 1 = e) :
    ∀ z : AE D, z * e = e * phiE v (compV v ι (finPart D z)) := by
  have hphi : ∀ x y, phiE v (x * y) = phiE v x * phiE v y := by
    intro x y
    simp only [phiE, map_mul]
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp [phiE]
  | tmul a w =>
    have hf : compV v ι (finPart D (a ⊗ₜ[D.host.F] w)) = evalV D.host.F v (sndA D.host.F a) * ι w := by
      simp [finPart, compV, Algebra.TensorProduct.lift_tmul]
    have ha : e * algebraMap (AF D.host.F) (AE D) a = e * phiE v (evalV D.host.F v (sndA D.host.F a)) := by
      have h0 : e * phiE v 1 = e := heps
      simp only [phiE] at h0 ⊢
      rw [← sA_one_mul, map_mul, ← mul_assoc, h0]
    rw [hf, hphi, tmul_eq]
    calc algebraMap (AF D.host.F) (AE D) a * incA D w * e
        = (e * incA D w) * algebraMap (AF D.host.F) (AE D) a := by ring
      _ = (e * phiE v (ι w)) * algebraMap (AF D.host.F) (AE D) a := by rw [hid]
      _ = (e * algebraMap (AF D.host.F) (AE D) a) * phiE v (ι w) := by ring
      _ = (e * phiE v (evalV D.host.F v (sndA D.host.F a))) * phiE v (ι w) := by rw [ha]
      _ = e * (phiE v (evalV D.host.F v (sndA D.host.F a)) * phiE v (ι w)) := by ring
  | add x y hx hy =>
    rw [add_mul, hx, hy, ← mul_add]
    congr 1
    simp only [phiE, map_add (f := _)]


set_option maxHeartbeats 1000000 in
theorem idem_data (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) :
    ∃ (e : AE D) (ι : D.host.E →ₐ[D.host.F] v.adicCompletion D.host.F), Formalism.L2.NTheta.IsIdemAt e P ∧
      IsPlaceIdem D v (sA v 1) ∧ e + cA D e = phiE v 1 ∧
      (∀ z : AE D, z * e = e * phiE v (compV v ι (finPart D z))) ∧ compV v ι (finPart D e) = 1 := by
  obtain ⟨b, tO, NO, hbP, hbsP, ht, hN, htv, hNv⟩ := split_datum P hP v hv
  obtain ⟨r₁, r₂, hsum, hprod, hr₁, hr₂⟩ := roots_exist v tO NO hNv htv
  obtain ⟨t', ht'⟩ : ∃ t', t' = algebraMap D.host.F (v.adicCompletion D.host.F) (tO : D.host.F) := ⟨_, rfl⟩
  obtain ⟨N', hN'⟩ : ∃ N', N' = algebraMap D.host.F (v.adicCompletion D.host.F) (NO : D.host.F) := ⟨_, rfl⟩
  have hsum' : r₁ + r₂ = t' := by rw [ht']; exact hsum
  have hprod' : r₁ * r₂ = N' := by rw [hN']; exact hprod
  have hbne : star (b : D.host.E) ≠ b := by
    intro h; apply hbsP
    have : starO b = b := FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E h
    rw [this]; exact hbP
  have hr : r₁ ^ 2 - ((tO : D.host.F) : v.adicCompletion D.host.F) * r₁ +
      ((NO : D.host.F) : v.adicCompletion D.host.F) = 0 := by
    rw [← hsum, ← hprod]; ring
  obtain ⟨ι, hι, hadj⟩ := emb_exists v (b : D.host.E) tO NO ht hN hbne r₁ hr
  have hd : r₁ - r₂ ≠ 0 := by
    intro h
    have h' : r₁ = r₂ := sub_eq_zero.1 h
    rw [h', hr₂] at hr₁
    exact lt_irrefl _ hr₁
  obtain ⟨y₀, hy⟩ : ∃ y₀ : v.adicCompletion D.host.F, y₀ * (r₁ - r₂) = 1 := ⟨(r₁ - r₂)⁻¹, inv_mul_cancel₀ hd⟩
  obtain ⟨x₀, hx⟩ : ∃ x₀ : v.adicCompletion D.host.F, x₀ = -r₂ * y₀ := ⟨_, rfl⟩

  have f1 : x₀ * x₀ - N' * (y₀ * y₀) - x₀ = 0 := by
    rw [hx, ← hprod']; linear_combination (-(r₂ * y₀)) * hy
  have f2 : x₀ * y₀ + x₀ * y₀ + t' * (y₀ * y₀) - y₀ = 0 := by
    rw [hx, ← hsum']; linear_combination y₀ * hy
  have f3 : x₀ * x₀ + t' * (x₀ * y₀) + N' * (y₀ * y₀) = 0 := by
    rw [hx, ← hsum', ← hprod']; ring
  have f4 : x₀ + x₀ + t' * y₀ = 1 := by
    rw [hx, ← hsum']; linear_combination hy
  have f5 : x₀ + y₀ * r₁ = 1 := by
    rw [hx]; linear_combination hy
  have f6 : x₀ + t' * y₀ - y₀ * r₁ = 0 := by
    rw [hx, ← hsum']; ring
  have f7 : x₀ * r₁ + N' * y₀ = 0 := by
    rw [hx, ← hprod']; ring

  obtain ⟨u, hu0⟩ : ∃ u : AE D, u = incA D (b : D.host.E) := ⟨_, rfl⟩
  obtain ⟨Tt, hTt⟩ : ∃ Tt : AE D, Tt = algebraMap D.host.F (AE D) (tO : D.host.F) := ⟨_, rfl⟩
  obtain ⟨Nn, hNn⟩ : ∃ Nn : AE D, Nn = algebraMap D.host.F (AE D) (NO : D.host.F) := ⟨_, rfl⟩
  have hu : u * u = Tt * u - Nn := by
    have hbb : (b : D.host.E) * b = algebraMap D.host.F D.host.E (tO : D.host.F) * b -
        algebraMap D.host.F D.host.E (NO : D.host.F) := by rw [ht, hN]; ring
    rw [hu0, hTt, hNn, ← map_mul, hbb, map_sub, map_mul, incA_alg, incA_alg]
  have hcu : cA D u = Tt - u := by
    have hs : star (b : D.host.E) = algebraMap D.host.F D.host.E (tO : D.host.F) - b := by rw [ht]; ring
    rw [hu0, hTt, cA_incA, hs, map_sub, incA_alg]
  have sT : ∀ a, Tt * phiE v a = phiE v (t' * a) := fun a => by rw [hTt, ht', phiE_smul]
  have sN : ∀ a, Nn * phiE v a = phiE v (N' * a) := fun a => by rw [hNn, hN', phiE_smul]
  have m : ∀ a c, phiE v a * phiE v c = phiE v (a * c) := fun a c => (phiE_mul v a c).symm
  have g1 : phiE v (x₀ * x₀) - phiE v (N' * (y₀ * y₀)) - phiE v x₀ = 0 := by
    have := congrArg (phiE v) f1; rwa [phiE_sub, phiE_sub, phiE_zero] at this
  have g2 : phiE v (x₀ * y₀) + phiE v (x₀ * y₀) + phiE v (t' * (y₀ * y₀)) - phiE v y₀ = 0 := by
    have := congrArg (phiE v) f2; rwa [phiE_sub, phiE_add, phiE_add, phiE_zero] at this
  have g3 : phiE v (x₀ * x₀) + phiE v (t' * (x₀ * y₀)) + phiE v (N' * (y₀ * y₀)) = 0 := by
    have := congrArg (phiE v) f3; rwa [phiE_add, phiE_add, phiE_zero] at this
  have g4 : phiE v x₀ + phiE v x₀ + phiE v (t' * y₀) = phiE v 1 := by
    have := congrArg (phiE v) f4; rwa [phiE_add, phiE_add] at this
  have g5 : phiE v x₀ + phiE v (y₀ * r₁) = phiE v 1 := by
    have := congrArg (phiE v) f5; rwa [phiE_add] at this
  have g6 : phiE v x₀ + phiE v (t' * y₀) - phiE v (y₀ * r₁) = 0 := by
    have := congrArg (phiE v) f6; rwa [phiE_sub, phiE_add, phiE_zero] at this
  have g7 : phiE v (x₀ * r₁) + phiE v (N' * y₀) = 0 := by
    have := congrArg (phiE v) f7; rwa [phiE_add, phiE_zero] at this

  obtain ⟨e, he⟩ : ∃ e : AE D, e = phiE v x₀ + phiE v y₀ * u := ⟨_, rfl⟩
  have hee : e * e = e := by
    rw [he]
    linear_combination (phiE v y₀ * phiE v y₀) * hu + m x₀ x₀ + (2 * u) * m x₀ y₀ + (Tt * u - Nn) * m y₀ y₀ +
      u * sT (y₀ * y₀) - sN (y₀ * y₀) + g1 + u * g2
  have hce : cA D e = phiE v x₀ + phiE v y₀ * (Tt - u) := by
    rw [he, map_add (f := _), map_mul, cA_phiE, cA_phiE, hcu]
  have hec : e * cA D e = 0 := by
    rw [hce, he]
    linear_combination (-(phiE v y₀ * phiE v y₀)) * hu + m x₀ x₀ + Tt * m x₀ y₀ + Nn * m y₀ y₀ + sT (x₀ * y₀) +
      sN (y₀ * y₀) + g3
  have hsume : e + cA D e = algebraMap (AF D.host.F) (AE D) (sA v 1) := by
    show e + cA D e = phiE v 1
    rw [hce, he]
    linear_combination sT y₀ + g4
  have hplace : IsPlaceIdem D v (sA v 1) := ⟨sglV v 1, rfl, sglV_same v 1, fun w hw => sglV_ne v 1 hw⟩

  have hcompe : compV v ι (finPart D e) = 1 := by
    rw [he, map_add (f := _), map_mul, map_add (f := _), map_mul, compV_phiE, compV_phiE, hu0, compV_incA, hι]
    exact f5
  have hιF : ∀ f : 𝓞 D.host.F, ι (algebraMap D.host.F D.host.E (f : D.host.F)) =
      ((f : D.host.F) : v.adicCompletion D.host.F) := fun f => ι.commutes _
  have hιs : ι (star (b : D.host.E)) = r₂ := by
    have hs : star (b : D.host.E) = algebraMap D.host.F D.host.E (tO : D.host.F) - b := by rw [ht]; ring
    rw [hs, map_sub, hιF, hι, ← hsum]; ring

  have hfwd : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal → Valued.v (ι (x : D.host.E)) < 1 := by
    intro x hxP
    have hz : x * starO b ∈ P.asIdeal := P.asIdeal.mul_mem_right _ hxP
    have hzs : starO (x * starO b) ∈ P.asIdeal := by
      have : starO (x * starO b) = b * starO x := by
        apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
        show star ((x : D.host.E) * star (b : D.host.E)) = (b : D.host.E) * star (x : D.host.E)
        rw [star_mul, star_star]
      rw [this]; exact P.asIdeal.mul_mem_right _ hbP
    obtain ⟨TF, hTF⟩ := fixed_int (x * starO b + starO (x * starO b)) (by
      show star ((x : D.host.E) * star (b : D.host.E) + star ((x : D.host.E) * star (b : D.host.E))) = _
      rw [star_add, star_star, add_comm]; rfl)
    obtain ⟨MF, hMF⟩ := fixed_int (x * starO b * starO (x * starO b)) (by
      show star ((x : D.host.E) * star (b : D.host.E) * star ((x : D.host.E) * star (b : D.host.E))) = _
      rw [star_mul, star_star]; rfl)
    have hTFv : TF ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap]
      have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) TF = x * starO b + starO (x * starO b) :=
        FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E hTF
      rw [this]; exact P.asIdeal.add_mem hz hzs
    have hMFv : MF ∈ v.asIdeal := by
      rw [← hv, Ideal.mem_comap]
      have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) MF = x * starO b * starO (x * starO b) :=
        FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E hMF
      rw [this]; exact P.asIdeal.mul_mem_right _ hz
    obtain ⟨z, hz0⟩ : ∃ z : D.host.E, z = (x : D.host.E) * star (b : D.host.E) := ⟨_, rfl⟩
    have hzq : ι z * ι z = ((TF : D.host.F) : v.adicCompletion D.host.F) * ι z - ((MF : D.host.F) : v.adicCompletion D.host.F) := by
      rw [← hιF, ← hιF, ← map_mul, ← map_mul, ← map_sub]
      congr 1
      have e1 : algebraMap D.host.F D.host.E (TF : D.host.F) = z + star z := by rw [hz0]; exact hTF
      have e2 : algebraMap D.host.F D.host.E (MF : D.host.F) = z * star z := by rw [hz0]; exact hMF
      rw [e1, e2]; ring
    have hvz : Valued.v (ι z) < 1 := by
      have hT : Valued.v (((TF : D.host.F) : v.adicCompletion D.host.F)) < 1 := (val_coe_lt_one_iff v TF).2 hTFv
      have hM : Valued.v (((MF : D.host.F) : v.adicCompletion D.host.F)) < 1 := (val_coe_lt_one_iff v MF).2 hMFv
      have hzle : Valued.v (ι z) ≤ 1 := by
        rw [hz0]
        exact val_emb_le v ι (x * starO b)
      have hsq : Valued.v (ι z * ι z) < 1 := by
        rw [hzq]
        refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ hM)
        rw [Valuation.map_mul]
        exact lt_of_lt_of_le (mul_lt_one_of_lt_of_le hT hzle) le_rfl
      by_contra hge
      push Not at hge
      rw [Valuation.map_mul] at hsq
      exact absurd (one_le_mul hge hge) (not_le.2 hsq)
    rw [hz0, map_mul, hιs, Valuation.map_mul, hr₂, mul_one] at hvz
    exact hvz
  have hιP : ∀ x : 𝓞 D.host.E, x ∈ P.asIdeal ↔ Valued.v (ι (x : D.host.E)) < 1 := by
    intro x
    refine ⟨hfwd x, fun hlt => ?_⟩
    by_contra hxP
    obtain ⟨y, i, hi, hyi⟩ := P.isMaximal.exists_inv hxP
    have h1 : ι ((y : D.host.E) * x) + ι (i : D.host.E) = 1 := by
      rw [← map_add (f := _)]
      have : ((y : D.host.E) * x + i) = 1 := by exact_mod_cast congrArg (fun w : 𝓞 D.host.E => (w : D.host.E)) hyi
      rw [this, map_one]
    have h2 : Valued.v (ι ((y : D.host.E) * x)) < 1 := by
      rw [map_mul, Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (val_emb_le v ι y)) hlt
    have h3 := hfwd i hi
    have h4 : Valued.v (ι ((y : D.host.E) * x) + ι (i : D.host.E)) < 1 :=
      lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt h2 h3)
    rw [h1, Valuation.map_one] at h4
    exact lt_irrefl _ h4

  have hid : ∀ w : D.host.E, e * incA D w = e * phiE v (ι w) := by
    intro w
    have hw : w ∈ Algebra.adjoin D.host.F {(b : D.host.E)} := by rw [hadj]; exact Algebra.mem_top
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [← hu0, hι, he]
      linear_combination phiE v y₀ * hu + u * sT y₀ - u * m y₀ r₁ + u * g6 - m x₀ r₁ - sN y₀ - g7
    | algebraMap f =>
      rw [incA_alg, AlgHom.commutes, he]
      have s1 := phiE_smul v f x₀
      have s2 := phiE_smul v f y₀
      have m1 : phiE v x₀ * phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f) =
          phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f * x₀) := by rw [mul_comm _ x₀, phiE_mul]
      have m2 : phiE v y₀ * phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f) =
          phiE v (algebraMap D.host.F (v.adicCompletion D.host.F) f * y₀) := by rw [mul_comm _ y₀, phiE_mul]
      linear_combination s1 + u * s2 - m1 - u * m2
    | add x y _ _ hx hy =>
      rw [map_add (f := _), mul_add, hx, hy, map_add (f := _), phiE_add, mul_add]
    | mul x y _ _ hx hy =>
      calc e * incA D (x * y) = (e * incA D x) * incA D y := by rw [map_mul, mul_assoc]
        _ = (e * phiE v (ι x)) * incA D y := by rw [hx]
        _ = (e * incA D y) * phiE v (ι x) := by ring
        _ = (e * phiE v (ι y)) * phiE v (ι x) := by rw [hy]
        _ = e * phiE v (ι (x * y)) := by rw [map_mul ι, phiE_mul]; ring
  have hy1 : Valued.v y₀ = 1 := by
    have h12 : Valued.v (r₁ - r₂) = 1 := by rw [Valuation.map_sub_eq_of_lt_right _ (by rw [hr₂]; exact hr₁), hr₂]
    have := congrArg Valued.v hy
    rwa [Valuation.map_mul, h12, mul_one, Valuation.map_one] at this
  have hx1 : Valued.v x₀ = 1 := by rw [hx, Valuation.map_mul, Valuation.map_neg, hr₂, hy1, mul_one]
  have heps : e * phiE v 1 = e := by
    have h : e * (e + cA D e) = e * phiE v 1 := by rw [hsume]; rfl
    rw [mul_add, hee, hec, add_zero] at h
    exact h.symm
  have hz := mul_e_of v e ι hid heps
  refine ⟨e, ι, ⟨⟨hee, hec, v, sA v 1, hplace, hsume⟩, ?_⟩, hplace, hsume, hz, hcompe⟩
  intro x hx0
  have hxE : (x : D.host.E) ≠ 0 := by exact_mod_cast hx0
  have hιx : ι (x : D.host.E) ≠ 0 := (map_ne_zero ι).2 hxE
  have hcomp : compV v ι (finPart D (e * incA D ((x : D.host.E)⁻¹))) = (ι (x : D.host.E))⁻¹ := by
    rw [map_mul, map_mul, hcompe, compV_incA, one_mul, map_inv₀]
  constructor
  · intro hxP hmem
    have h1 := compV_int v ι hmem
    rw [hcomp, map_inv₀] at h1
    have h2 := hfwd x hxP
    have hne : Valued.v (ι (x : D.host.E)) ≠ 0 := (Valuation.ne_zero_iff _).2 hιx
    have h4 : 1 ≤ Valued.v (ι (x : D.host.E)) := by
      have h5 := mul_le_mul' h1 (le_refl (Valued.v (ι (x : D.host.E))))
      rwa [inv_mul_cancel₀ hne, one_mul] at h5
    exact absurd h2 (not_lt.2 h4)
  · intro hnot
    by_contra hxP
    apply hnot
    have hv1 : Valued.v (ι (x : D.host.E)) = 1 :=
      le_antisymm (val_emb_le v ι x) (not_lt.1 fun h => hxP ((hιP x).2 h))
    obtain ⟨c, hc⟩ : ∃ c, c = ι ((x : D.host.E)⁻¹) := ⟨_, rfl⟩
    have hc1 : Valued.v c = 1 := by rw [hc, map_inv₀, map_inv₀, hv1, inv_one]
    rw [hid, ← hc, he, add_mul, mul_assoc, mul_comm u, ← mul_assoc, ← phiE_mul, ← phiE_mul, map_add (f := _), map_mul,
      finPart_phiE, finPart_phiE, hu0, finPart_incA, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    refine add_mem (AddSubgroup.subset_closure ⟨sglV v (x₀ * c), sglV_int v ?_, 1, by simp⟩)
      (AddSubgroup.subset_closure ⟨sglV v (y₀ * c), sglV_int v ?_, b, rfl⟩)
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hx1, hc1, mul_one]
    · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, hy1, hc1, mul_one]

theorem idem_at (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P)
    (v : HeightOneSpectrum (𝓞 D.host.F))
    (hv : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal) :
    ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e P ∧
      ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, -, he, hpl, hs, -, -⟩ := idem_data P hP v hv
  exact ⟨e, he, sA v 1, hpl, hs⟩

end Main

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

instance intEF : Algebra.IsIntegral (𝓞 D.host.F) (𝓞 D.host.E) := inferInstance

def belowPl (P : HeightOneSpectrum (𝓞 D.host.E)) : HeightOneSpectrum (𝓞 D.host.F) where
  asIdeal := P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hxP (Algebra.IsIntegral.isIntegral x)

theorem idem_exists_at (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ¬ Lev.IsConjPl (D := D) P P) :
    ∃ e : AE D, Formalism.L2.NTheta.IsIdemAt e P ∧
      ∀ v : HeightOneSpectrum (𝓞 D.host.F), P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal →
        ∃ ε : AF D.host.F, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, ε, hε, heq⟩ := idem_at P hP (belowPl P) rfl
  refine ⟨e, he, fun v hv => ⟨ε, ?_, heq⟩⟩
  have hb : belowPl P = v := HeightOneSpectrum.ext hv
  exact hb ▸ hε

theorem twoSplitIdem (D : D7) : TwoSplitIdem D := by
  have hTS : TwoSplits D := by
    exact twoSplits D
  have hinj : Function.Injective (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    exact FaithfulSMul.algebraMap_injective _ _
  intro v hv
  have hker : RingHom.ker (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≤ v.asIdeal := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral v.asIdeal hker
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQ, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQm.isPrime, hQ0⟩
  have h2 : (2 : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h2' : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) 2 ∈ Q := by
      rw [← Ideal.mem_comap]
      change (2 : 𝓞 D.host.F) ∈ Ideal.under (𝓞 D.host.F) Q
      rw [hQ]
      exact hv
    rw [map_ofNat] at h2'
    exact h2'
  obtain ⟨e, he, hall⟩ := idem_exists_at P (hTS P h2)
  obtain ⟨ε, hε, heq⟩ := hall v hQ
  exact ⟨e, ε, he.1, hε, heq⟩

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SbHalfHalfInd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitOrInert (D : D7) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    (∃ PP : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal ∧
      ¬ Lev.IsConjPl (D := D) PP PP) ∨
    ∀ e : AE D, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0


open Classical in
theorem sbHalf_halfInd {S T : HSp D} (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  unfold IsSBHalf halfInd
  refine ⟨?_, 1, one_pos, ?_⟩
  · intro t ht
    by_contra hn
    apply ht
    simp [hn]
  · refine ⟨?_, ?_⟩
    · intro u hu hh t
      have hΛ : t + 1 • u ∈ Λ ↔ t ∈ Λ := by
        rw [one_smul]
        exact ⟨fun h => by simpa using Λ.sub_mem h hu, fun h => Λ.add_mem h hu⟩
      have hH : IsHalf e (t + 1 • u) ↔ IsHalf e t := by
        unfold IsHalf at hh ⊢
        simp only [one_smul, Matrix.add_apply, Pi.add_apply, mul_add, hh, add_left_inj]
      simp only [hΛ, hH]
    · intro t ht
      rw [one_smul]
      by_contra hn
      apply ht
      simp [hn]

theorem fix_split (hSL : SplitLin D) (hPM : PlaceModelAt D) {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}
    {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {PP : Formalism.L2.DIV.Pl D.host.E} {e' : AE D}
    (he' : Formalism.L2.NTheta.IsIdemAt e' PP) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀)
    (hn : ∃ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 ∧ nrm2 μ 𝓕 f₀ = 1)
    {g : GA D S} {h : GA D T} (hg : SuppAt e' S g) (hh : SuppAt e' T h) {x y : (AE D)ˣ}
    (hx : IsDetAt e' S g x) (hy : IsDetAt e' T h y) (hfac : splitFacO χS χT x y = 1)
    (hpres : ∀ t : WO S T, IsHalf e' t → (actO S T g h t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT))
    (hpres' : ∀ t : WO S T, IsHalf e' t → (actO S T g⁻¹ h⁻¹ t ∈ latAll S T ΛS ΛT ↔ t ∈ latAll S T ΛS ΛT)) :
    om (g, h) f₀ = f₀ := by
  classical
  have hsp : IsSplitIdem D e' := he'.1
  have hsum : IsIdemSum e' {PP} := by
    refine ⟨⟨fun _ => e', fun Q hQ => ?_, by simp⟩, hsp.2.1⟩
    rw [Finset.mem_singleton] at hQ
    subst hQ
    exact he'
  have hvac : ∀ u ∈ latAll S T ΛS ΛT, (IsHalf e' u ∨ IsHalf (cA D e') u) →
      heisO ψ S T u f₀ = f₀ := by
    intro u hu hh
    rcases hh with hh | hh
    · exact hlat.2 e' hsp u hu hh
    · exact hlat.2 (cA D e') (isSplitIdem_cA hsp) u hu hh
  obtain ⟨Tm, hTm, -, -, -⟩ :=
    hPM ψ hW.std S T ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac e' (Or.inl rfl)
  obtain ⟨r, -, hrep, hr1⟩ := hSL ψ S T χS χT om hW ΛS ΛT hsS hsT {PP} e' hsum f₀ hf₀ hvac Tm hTm
    e' hsp hsp.1 g h hg hh x y hx hy
  have hr : r = 1 := hr1 hpres hn
  have hΦ : IsSBHalf e' (latAll S T ΛS ΛT) ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) := by
    rw [one_smul]
    exact sbHalf_halfInd e' _
  have hinv : (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) =
      (1 : ℂ) • halfInd e' (latAll S T ΛS ΛT) := by
    funext t
    simp only [one_smul, halfInd]
    by_cases ht : IsHalf e' t
    · have h1 : IsHalf e' (actO S T g⁻¹ h⁻¹ t) := (isHalf_actO g⁻¹ h⁻¹ t).2 ht
      simp only [hpres' t ht, h1, ht, and_true]
    · have h1 : ¬ IsHalf e' (actO S T g⁻¹ h⁻¹ t) := fun h' => ht ((isHalf_actO g⁻¹ h⁻¹ t).1 h')
      simp only [h1, ht, and_false, if_false]
  calc om (g, h) f₀ = om (g, h) (Tm ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT))) := by rw [hTm.vac]
    _ = ((r : ℂ) * (splitFacO χS χT x y : ℂ)) •
          Tm (fun t => ((1 : ℂ) • halfInd e' (latAll S T ΛS ΛT)) (actO S T g⁻¹ h⁻¹ t)) := hrep _ hΦ
    _ = f₀ := by
      rw [hinv, hTm.vac, hr, hfac]
      simp

theorem latO_le_all {S T : HSp D} (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T ΛS ΛT P ≤ latO S T ΛS ΛT (fun _ => True) := by
  unfold latO
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, h1, h2⟩
  refine ⟨α, hα, ?_, h2⟩
  intro v
  first
    | exact fun h => absurd trivial h
    | simp
    | simp_all
    | aesop

theorem fix_inert {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hI : WeilFull.SphInertAtO ψ S T χS χT om)
    (hrk : S.rank ≠ T.rank) (hev : Even S.rank ∨ Even T.rank)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hsS : IsSelfDualC S ΛS) (hsT : IsSelfDualC T ΛT) {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hfS : Formalism.L2.DIV.IsFrame βS ΛS) (hfT : Formalism.L2.DIV.IsFrame βT ΛT) {v : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) (h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal)
    (hin : ∀ e, IsSplitIdem D e → e * algebraMap (AF D.host.F) (AE D) ε = 0)
    (huS : WeilFull.UnrAtV ε χS) (huT : WeilFull.UnrAtV ε χT) {g : GA D S} {h : GA D T}
    (hg : WeilFull.SuppV ε S g) (hh : WeilFull.SuppV ε T h) (hgS : Lev.finE S g ∈ Formalism.L2.DIV.St βS)
    (hhT : Lev.finE T h ∈ Formalism.L2.DIV.St βT) {f₀ : WO S T → ℂ} (hf₀ : IsThetaFunO ψ S T f₀)
    (hlat : IsLatVac (heisO ψ S T) (latAll S T ΛS ΛT) f₀) : om (g, h) f₀ = f₀ := by
  have key : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun w => w = v) f₀ := by
    clear * - hlat
    unfold IsLatVac at *
    exact ⟨fun u hu => hlat.1 u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu),
      fun e he u hu hh => hlat.2 e he u (latO_le_all (S := S) (T := T) ΛS ΛT _ hu) hh⟩
  exact hI hrk hev ΛS ΛT hsS hsT βS βT hfS hfT v ε hε h2 hin huS huT g h hg hh hgS hhT f₀ hf₀ key

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end
