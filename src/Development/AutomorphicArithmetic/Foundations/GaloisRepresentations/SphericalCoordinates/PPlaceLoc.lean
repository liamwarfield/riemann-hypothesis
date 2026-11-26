module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionPointTorusExtensionEqOfLiesOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCompletionEqLatticeVectorAddNsmul

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PPlaceLoc
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

private theorem formB_add_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β (a + b) c = formB L β a c + formB L β b c := by
  simp only [formB, map_add (f := _), LinearMap.add_apply]

private theorem formB_nsmul_left {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β (n • a) c = n * formB L β a c := by
  simp only [formB, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]

private theorem formB_add_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (a b c : VQ D) : formB L β a (b + c) = formB L β a b + formB L β a c := by
  simp only [formB, map_add (f := _)]

private theorem formB_nsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℕ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_nsmul, nsmul_eq_mul]

private theorem formB_zsmul_right {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (β : G.Cˣ)
    (n : ℤ) (a c : VQ D) : formB L β a (n • c) = n * formB L β a c := by
  simp only [formB, map_zsmul, zsmul_eq_mul]

private theorem den_dvd_of_mul_eq_int (q : ℚ) (n : ℕ) (z : ℤ) (h : (n : ℚ) * q = z) : q.den ∣ n := by
  have h1 : (n : ℤ) * q.num = z * q.den := by
    have h2 : (q.num : ℚ) = q * q.den := (Rat.mul_den_eq_num q).symm
    have h3 : (((n : ℤ) * q.num : ℤ) : ℚ) = ((z * q.den : ℤ) : ℚ) := by
      push_cast
      rw [h2, ← _root_.mul_assoc, h]
    exact_mod_cast h3
  have h3 : (q.den : ℤ) ∣ n * q.num := ⟨z, by rw [h1]; ring⟩
  have h4 : IsCoprime (q.den : ℤ) q.num := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
    exact q.reduced
  exact Int.natCast_dvd_natCast.1 (h4.dvd_of_dvd_mul_right h3)

theorem placeLoc_of : PlaceLoc := by
  intro p _ D G L β D' j hP hH
  obtain ⟨-, hact, hspan, s0, hs0, hform⟩ := hP
  obtain ⟨E₁, hE, e, he, hperf⟩ := hH
  have hE1 : ∀ u u', (E₁ u u' : ℚ) = (s0 / 2) * formB L β (j u) (j u') := by
    intro u u'
    have h := hform u u'
    rw [hE] at h
    simp only [LinearMap.smul_apply, smul_eq_mul] at h
    push_cast at h
    linarith
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ D'.La).FG)
  have hcl0 : AddSubgroup.closure (S : Set D'.La) = ⊤ := by
    rw [eq_top_iff]
    intro u _
    have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
    induction hu using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | smul a x _ hx => exact zsmul_mem (hx trivial) a
  have hcl : AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) = j.range := by
    rw [Finset.coe_image, ← AddMonoidHom.map_closure, hcl0, AddMonoidHom.range_eq_map]
  let M : AddSubgroup (VQ D) :=
    { carrier := {w | ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u}
      add_mem' := by
        rintro a b ⟨m, u, hm, hu⟩ ⟨m', u', hm', hu'⟩
        refine ⟨m * m', m' • u + m • u', hm.mul_left hm', ?_⟩
        rw [map_add (f := _), map_nsmul, map_nsmul, ← hu, ← hu', smul_add, smul_smul, smul_smul, mul_comm m' m]
      zero_mem' := ⟨1, 0, Nat.coprime_one_left p, by simp⟩
      neg_mem' := by
        rintro a ⟨m, u, hm, hu⟩
        exact ⟨m, -u, hm, by rw [map_neg, ← hu, smul_neg]⟩ }
  have hM : ∀ w, w ∈ M ↔ ∃ (m : ℕ) (u : D'.La), m.Coprime p ∧ m • w = j u := fun w => Iff.rfl
  refine ⟨M, ⟨?_, S.image j, ?_, ?_⟩, ⟨s0 / 2, by positivity, ?_⟩, fun w => (hM w).symm⟩
  · rintro c w ⟨m, u, hm, h⟩
    exact ⟨m, c • u, hm, by rw [hact, ← h, map_nsmul]⟩
  · rw [eq_top_iff]
    intro w _
    obtain ⟨m, u, hm, h⟩ := hspan w
    have hu : j u ∈ AddSubgroup.closure ((S.image j : Finset (VQ D)) : Set (VQ D)) := hcl ▸ ⟨u, rfl⟩
    have hu' : j u ∈ Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D)) :=
      (AddSubgroup.closure_le (Submodule.span ℚ ((S.image j : Finset (VQ D)) : Set (VQ D))).toAddSubgroup).2
        Submodule.subset_span hu
    have hw : w = (m : ℚ)⁻¹ • j u := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hm), one_smul]
    rw [hw]
    exact Submodule.smul_mem _ _ hu'
  · intro w
    rw [hcl]
    constructor
    · rintro ⟨m, u, hm, h⟩
      exact ⟨m, hm, ⟨u, h.symm⟩⟩
    · rintro ⟨m, hm, u, h⟩
      exact ⟨m, u, hm, h.symm⟩
  · intro w
    constructor
    · rintro ⟨m, a, hm, ha⟩ u ⟨m', b, hm', hb⟩
      have key : ((m * m' : ℕ) : ℚ) * (s0 / 2 * formB L β w u) = (E₁ a b : ℤ) := by
        rw [hE1, ← ha, ← hb, formB_nsmul_left, formB_nsmul_right]
        push_cast
        ring
      exact Nat.Coprime.coprime_dvd_left (den_dvd_of_mul_eq_int _ _ _ key) (hm.mul_left hm')
    · intro h
      have hden : ∀ x : D'.La, (s0 / 2 * formB L β w (j x)).den.Coprime p := fun x =>
        h (j x) ⟨1, x, Nat.coprime_one_left p, one_smul _ _⟩
      let m : ℕ := ∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den
      have hm : m.Coprime p := Nat.Coprime.prod_left fun x _ => hden x
      have hint : ∀ u : D'.La, ∃ z : ℤ, (z : ℚ) = m * (s0 / 2 * formB L β w (j u)) := by
        intro u
        have hu : u ∈ Submodule.span ℤ (S : Set D'.La) := hS ▸ Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem (fun x => (s0 / 2 * formB L β w (j x)).den) hx
          refine ⟨r * (s0 / 2 * formB L β w (j x)).num, ?_⟩
          have h2 := Rat.mul_den_eq_num (s0 / 2 * formB L β w (j x))
          change (((r : ℤ) * (s0 / 2 * formB L β w (j x)).num : ℤ) : ℚ) = ((∏ x ∈ S, (s0 / 2 * formB L β w (j x)).den : ℕ) : ℚ) * _
          rw [hr]
          push_cast
          rw [← h2]
          ring
        | zero =>
          refine ⟨0, ?_⟩
          have h0 : formB L β w (j 0) = 0 := by
            have := formB_nsmul_right L β 0 w (0 : VQ D)
            simpa using this
          rw [h0]
          simp
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          refine ⟨a + b, ?_⟩
          rw [map_add (f := _), formB_add_right]
          push_cast
          rw [ha, hb]
          ring
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          refine ⟨a * b, ?_⟩
          rw [map_zsmul, formB_zsmul_right]
          push_cast
          rw [hb]
          ring
      choose c hc using hint
      let f : D'.La →ₗ[ℤ] ℤ := AddMonoidHom.toIntLinearMap (AddMonoidHom.mk' c (fun a b => by
        have h3 : ((c (a + b) : ℤ) : ℚ) = ((c a + c b : ℤ) : ℚ) := by
          push_cast
          rw [hc, hc, hc, map_add (f := _), formB_add_right]
          ring
        exact_mod_cast h3))
      obtain ⟨x, hx⟩ := hperf f
      obtain ⟨z, hz⟩ : ∃ z, z + j x = (e * m) • w := ⟨(e * m) • w - j x, sub_add_cancel _ _⟩
      have hs : s0 / 2 ≠ 0 := by positivity
      have hzero : ∀ u, formB L β z (j u) = 0 := by
        intro u
        have h1 : E₁ x u = e • c u := by
          have := LinearMap.congr_fun hx u
          simpa [f] using this
        have h2 : (E₁ x u : ℚ) = e * (m * (s0 / 2 * formB L β w (j u))) := by
          rw [h1, ← hc]
          push_cast
          simp
        rw [hE1] at h2
        have h3 : formB L β (z + j x) (j u) = ((e * m : ℕ) : ℚ) * formB L β w (j u) := by
          rw [hz, formB_nsmul_left]
        rw [formB_add_left] at h3
        have h4 : s0 / 2 * formB L β z (j u) = 0 := by
          have h5 : s0 / 2 * (formB L β z (j u) + formB L β (j x) (j u)) =
              s0 / 2 * (((e * m : ℕ) : ℚ) * formB L β w (j u)) := by rw [h3]
          push_cast at h5
          linarith
        exact (mul_eq_zero.1 h4).resolve_left hs
      obtain ⟨k, u₁, hk, hu₁⟩ := hspan z
      have hEF : ∀ u, D'.EF u₁ u = 0 := by
        intro u
        have h1 := hform u₁ u
        rw [← hu₁, formB_nsmul_left, hzero u] at h1
        simpa using h1
      have hu₀ : u₁ = 0 := D'.nondeg _ hEF
      have hz0 : z = 0 := by
        rw [hu₀, map_zero, ← Nat.cast_smul_eq_nsmul ℚ] at hu₁
        exact (smul_eq_zero.1 hu₁).resolve_left (by exact_mod_cast hk)
      refine ⟨e * m, x, he.mul_left hm, ?_⟩
      rw [← hz, hz0, zero_add]

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PIsogForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

private theorem herm_add_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (x a b : Fin g → ℂ) :
    hermForm M x (a + b) = hermForm M x a + hermForm M x b := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

private theorem herm_add_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (a b y : Fin g → ℂ) :
    hermForm M (a + b) y = hermForm M a y + hermForm M b y := by
  simp [hermForm, add_dotProduct]

private theorem herm_smul_right {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (x a : Fin g → ℂ) :
    hermForm M x (c • a) = star c * hermForm M x a := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

private theorem herm_smul_left {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (a y : Fin g → ℂ) :
    hermForm M (c • a) y = c * hermForm M a y := by
  simp only [hermForm, smul_dotProduct, smul_eq_mul]

private theorem herm_sub_smul {g : ℕ} (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (t : ℂ) (x y : Fin g → ℂ) :
    hermForm (H₁ - t • H₂) x y = hermForm H₁ x y - t * hermForm H₂ x y := by
  simp [hermForm, Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul]

private theorem real_smul_eq {g : ℕ} (c : ℝ) (a : Fin g → ℂ) : c • a = (c : ℂ) • a := by
  ext i; simp

private theorem herm_im_zero {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (h : ∀ x ∈ s, ∀ y ∈ s, (hermForm M x y).im = 0) (z w : Fin g → ℂ) :
    (hermForm M z w).im = 0 := by
  have key : ∀ w ∈ s, ∀ z, (hermForm M z w).im = 0 := by
    intro w hw z
    have hz : z ∈ Submodule.span ℝ s := by rw [hs]; trivial
    induction hz using Submodule.span_induction with
    | mem x hx => exact h x hx w hw
    | zero => simp [hermForm]
    | add a b _ _ ha hb => rw [herm_add_left]; simp [ha, hb]
    | smul c a _ ha => rw [real_smul_eq, herm_smul_left]; simp [ha]
  have hw : w ∈ Submodule.span ℝ s := by rw [hs]; trivial
  induction hw using Submodule.span_induction with
  | mem y hy => exact key y hy z
  | zero => simp [hermForm]
  | add a b _ _ ha hb => rw [herm_add_right]; simp [ha, hb]
  | smul c a _ ha => rw [real_smul_eq, herm_smul_right]; simp [ha]

private theorem bil_dvd {M : Type} [AddCommGroup M] (Bf : LinearMap.BilinForm ℤ M) (n : ℕ) (x y e e' : M) :
    (n : ℤ) ∣ Bf (x + n • e) (y + n • e') - Bf x y := by
  refine ⟨Bf x e' + Bf e y + n * Bf e e', ?_⟩
  simp [map_add (f := _), map_nsmul, LinearMap.add_apply, nsmul_eq_mul]
  ring

private theorem form_step {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf) (n : ℕ)
    {a a' b b' : D.La} {w w' : AfP p ⊗[ℚ] VQ D} (hw : w ∈ LaHat D) (hw' : w' ∈ LaHat D)
    (e : L.actG h (inAf D a) = inAf D b + n • w) (e' : L.actG h (inAf D a') = inAf D b' + n • w') :
    ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
      ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
  have h1 := MultScale.EFA_actG L h (inAf D a) (inAf D a')
  rw [e, e', MultScale.EFA_inAf] at h1
  simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul,
    MultScale.EFA_inAf] at h1
  have hn : IsIntAf (n : AfP p) := by
    have := MultScale.isIntAf_intCast (p := p) (n : ℤ)
    simpa using this
  refine ⟨-(MultScale.EFA D (inAf D b) w' + MultScale.EFA D w (inAf D b') +
    (n : AfP p) * MultScale.EFA D w w'), ?_, ?_⟩
  · exact MultScale.isIntAf_neg (MultScale.isIntAf_add (MultScale.isIntAf_add
      (MultScale.isIntAf_EFA D (MultScale.inAf_mem D b) hw')
      (MultScale.isIntAf_EFA D hw (MultScale.inAf_mem D b')))
      (MultScale.isIntAf_mul hn (MultScale.isIntAf_EFA D hw hw')))
  · linear_combination h1

private theorem cross_dvd {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) (n : ℕ) (hn : 0 < n) (hc : n.Coprime p) :
    (n : ℤ) ∣ D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  unfold IsWit at hf hf''
  have hX : ∀ x x' : D'.La, ∃ b b' a a' : D.La,
      (D''.EF (inc x) (inc x') ≡ nu'' n * (2 * D.EF b b') [ZMOD n]) ∧
      (D'.EF x x' ≡ nu n * (2 * D.EF a a') [ZMOD n]) ∧
      ∃ i : AfP p, IsIntAf i ∧ ((D.EF b b' : ℤ) : AfP p) =
        ((uSimR (AfP p) h : (AfP p)ˣ) : AfP p) * ((D.EF a a' : ℤ) : AfP p) + (n : AfP p) * i := by
    intro x x'
    obtain ⟨a, e, rfl⟩ := (hf.2 n hn hc).2.2.2.1 x
    obtain ⟨a', e', rfl⟩ := (hf.2 n hn hc).2.2.2.1 x'
    obtain ⟨b, E, hb⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a))
    obtain ⟨b', E', hb'⟩ := (hf''.2 n hn hc).2.2.2.1 (inc (f n a'))
    obtain ⟨w, hw, hwe⟩ := (hyp n hn hc a b).1 ⟨E, hb⟩
    obtain ⟨w', hw', hwe'⟩ := (hyp n hn hc a' b').1 ⟨E', hb'⟩
    refine ⟨b, b', a, a', ?_, ?_, form_step L h n hw hw' hwe hwe'⟩
    · have h1 : inc (f n a + n • e) = f'' n b + n • (E + inc e) := by
        rw [map_add (f := _), map_nsmul, hb, smul_add, add_assoc]
      have h2 : inc (f n a' + n • e') = f'' n b' + n • (E' + inc e') := by
        rw [map_add (f := _), map_nsmul, hb', smul_add, add_assoc]
      rw [h1, h2]
      exact (Int.modEq_iff_dvd.mpr (bil_dvd D''.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf''.2 n hn hc).2.2.2.2 b b')).symm
    · exact (Int.modEq_iff_dvd.mpr (bil_dvd D'.EF n _ _ _ _)).symm.trans
        (Int.modEq_iff_dvd.mpr ((hf.2 n hn hc).2.2.2.2 a a')).symm
  obtain ⟨b1, b2, a1, a2, hX1, hY1, i12, hi12, he12⟩ := hX u₁ u₂
  obtain ⟨b3, b4, a3, a4, hX3, hY3, i34, hi34, he34⟩ := hX u₃ u₄
  have hZ : (n : ℤ) ∣ D.EF b1 b2 * D.EF a3 a4 - D.EF b3 b4 * D.EF a1 a2 := by
    apply IntDvd.int_dvd_of_eq_mul_isIntAf p n hn hc _
      (i12 * ((D.EF a3 a4 : ℤ) : AfP p) - i34 * ((D.EF a1 a2 : ℤ) : AfP p))
    · rw [sub_eq_add_neg]
      exact MultScale.isIntAf_add (MultScale.isIntAf_mul hi12 (MultScale.isIntAf_intCast _))
        (MultScale.isIntAf_neg (MultScale.isIntAf_mul hi34 (MultScale.isIntAf_intCast _)))
    · rw [map_intCast]
      push_cast
      linear_combination ((D.EF a3 a4 : ℤ) : AfP p) * he12 - ((D.EF a1 a2 : ℤ) : AfP p) * he34
  have h0 : nu'' n * (2 * D.EF b1 b2) * (nu n * (2 * D.EF a3 a4)) -
      nu'' n * (2 * D.EF b3 b4) * (nu n * (2 * D.EF a1 a2)) ≡ 0 [ZMOD n] := by
    apply Int.modEq_zero_iff_dvd.mpr
    obtain ⟨k, hk⟩ := hZ
    exact ⟨4 * nu'' n * nu n * k, by linear_combination (4 * nu'' n * nu n) * hk⟩
  exact Int.modEq_zero_iff_dvd.mp (((hX1.mul hY3).sub (hX3.mul hY1)).trans h0)

private theorem cross {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (h : G.GAf)
    {D' D'' : PLat D.O D.inv} (inc : D'.La →ₗ[D.O] D''.La) {f : ℕ → D.La →+ D'.La} {nu : ℕ → ℤ}
    {f'' : ℕ → D.La →+ D''.La} {nu'' : ℕ → ℤ} (hf : IsWit D' f nu) (hf'' : IsWit D'' f'' nu'')
    (hyp : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ a b : D.La,
      (∃ u, inc (f n a) = f'' n b + n • u) ↔ ∃ w ∈ LaHat D, L.actG h (inAf D a) = inAf D b + n • w)
    (u₁ u₂ u₃ u₄ : D'.La) :
    D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ = D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ := by
  set d := D''.EF (inc u₁) (inc u₂) * D'.EF u₃ u₄ - D''.EF (inc u₃) (inc u₄) * D'.EF u₁ u₂ with hd
  suffices hz : d = 0 by exact sub_eq_zero.mp hz
  have hn : 0 < p * d.natAbs + 1 := Nat.succ_pos _
  have hc : (p * d.natAbs + 1).Coprime p :=
    ((Nat.coprime_mul_left_add_right p 1 d.natAbs).mpr (Nat.coprime_one_right p)).symm
  have hdvd := cross_dvd L h inc hf hf'' hyp u₁ u₂ u₃ u₄ _ hn hc
  apply Int.eq_zero_of_abs_lt_dvd hdvd
  have hp : (2 : ℤ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  rw [Int.abs_eq_natAbs]
  push_cast
  nlinarith [Int.natCast_nonneg d.natAbs]

theorem UpperTheory.Gal.W2.isogForm_of :
    UpperTheory.Gal.W2.RdForm → UpperTheory.Gal.W2.IsogForm := by
  intro _ p _ D G L h ρ D' D'' P P'' inc hP hP'' hPinc f nu f'' nu'' hf hf'' hyp
  by_cases hall : ∀ u u' : D'.La, D'.EF u u' = 0
  · refine ⟨1, one_pos, fun u u' => ?_⟩
    have h0 : ∀ x : D'.La, x = 0 := fun x => D'.nondeg x (hall x)
    rw [h0 u]
    simp
  push_neg at hall
  obtain ⟨u₃, u₄, hne⟩ := hall
  have hrel : ∀ u u' : D'.La, ((D''.EF (inc u) (inc u') : ℤ) : ℚ) =
      ((D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ)) * (D'.EF u u' : ℚ) := by
    intro u u'
    have hcq : ((D'.EF u₃ u₄ : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hne
    rw [div_mul_eq_mul_div, eq_div_iff hcq]
    exact_mod_cast cross L h inc hf hf'' hyp u u' u₃ u₄
  refine ⟨(D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ), ?_, hrel⟩
  unfold PELU.IsPeriod at hP hP''
  obtain ⟨-, hPinj, -, hspan, H1, -, hpos1, him1⟩ := hP
  obtain ⟨-, -, -, -, H2, -, hpos2, him2⟩ := hP''
  set q : ℚ := (D''.EF (inc u₃) (inc u₄) : ℚ) / (D'.EF u₃ u₄ : ℚ) with hq
  have hzero : ∀ z w, (hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w).im = 0 := by
    apply herm_im_zero _ (Set.range P) hspan
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [herm_sub_smul, Complex.sub_im, Complex.im_ofReal_mul, him1, ← hPinc x, ← hPinc y, him2]
    have hr : ((D''.EF (inc x) (inc y) : ℤ) : ℝ) = (q : ℝ) * ((D'.EF x y : ℤ) : ℝ) := by
      have := congrArg (fun t : ℚ => (t : ℝ)) (hrel x y)
      simpa [hq] using this
    rw [hr]
    ring
  have hM : ∀ z w, hermForm (H2 - ((q : ℝ) : ℂ) • H1) z w = 0 := by
    intro z w
    apply Complex.ext
    · have := hzero (Complex.I • z) w
      rw [herm_smul_left] at this
      simpa using this
    · simpa using hzero z w
  have hu3 : P u₃ ≠ 0 := by
    intro h0
    have hu : u₃ = 0 := hPinj (by rw [h0, map_zero])
    apply hne
    rw [hu]
    simp
  have e := hM (P u₃) (P u₃)
  rw [herm_sub_smul, sub_eq_zero] at e
  have p1 := hpos1 _ hu3
  have p2 := hpos2 _ hu3
  rw [e, Complex.re_ofReal_mul] at p2
  have hpos : (0 : ℝ) < (q : ℝ) := lt_of_not_ge (fun hle => by nlinarith)
  exact Rat.cast_pos.mp hpos
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PFixFinite
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
open GlobalTheory.CechDR GlobalTheory.HodgeCoh KaehlerDifferential GlobalTheory.Points

namespace UpperTheory.Gal.W2

private theorem iso_alg {R : Type} [CommRing R] [Algebra ℂ R] [IsNoetherianRing R] {d : ℕ}
    (e : R →ₐ[ℂ] ℂ) (φ : Ω[R⁄ℂ] →ₗ[ℂ] (Fin d → ℂ))
    (hk : ∀ ω : Ω[R⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → R) (ω' : Fin m → Ω[R⁄ℂ]),
      (∀ i, e (b i) = 0) ∧ ω = ∑ i, b i • ω' i)
    (g : Fin d → R) (hg : ∀ j, e (g j) = 0) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ j, φ (D ℂ R (g j)) = M j) (hdet : M.det ≠ 0) :
    ∃ r : R, e r = 1 ∧ ∀ e' : R →ₐ[ℂ] ℂ, (∀ j, e' (g j) = 0) → e' r ≠ 0 → e' = e := by
  classical
  set m : Ideal R := RingHom.ker e with hm
  set Ig : Ideal R := Ideal.span (Set.range g) with hIgEq
  have hmem : ∀ x, x ∈ m ↔ e x = 0 := fun x => RingHom.mem_ker
  have hsub : ∀ x : R, x - algebraMap ℂ R (e x) ∈ m := fun x => by
    rw [hmem, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  let dl : R →ₗ[ℂ] R ⧸ m ^ 2 :=
    { toFun := fun x => Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x))
      map_add' := fun x y => by
        simp only [map_add (f := _), map_sub]
        ring
      map_smul' := fun c x => by
        simp only [RingHom.id_apply, Algebra.smul_def, map_mul, map_sub, AlgHom.commutes,
          Ideal.Quotient.mk_algebraMap, Algebra.algebraMap_self]
        ring }
  let dd : Derivation ℂ R (R ⧸ m ^ 2) := Derivation.mk' dl (fun a b => by
    simp only [dl, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
    rw [← map_mul, ← map_mul, ← map_add (f := _), Ideal.Quotient.eq]
    have h2 : (a - algebraMap ℂ R (e a)) * (b - algebraMap ℂ R (e b)) ∈ m ^ 2 := by
      rw [pow_two]
      exact Ideal.mul_mem_mul (hsub a) (hsub b)
    convert (m ^ 2).neg_mem_iff.mpr h2 using 1
    simp only [map_mul]
    ring)
  have hd : ∀ x, dd x = Ideal.Quotient.mk (m ^ 2) (x - algebraMap ℂ R (e x)) := fun x => rfl
  have hL : ∀ x, dd.liftKaehlerDifferential (D ℂ R x) = dd x := fun x =>
    Derivation.liftKaehlerDifferential_comp_D dd x
  have hkill : ∀ b ∈ m, ∀ ω, b • dd.liftKaehlerDifferential ω = 0 := by
    intro b hb
    have hz : (b • dd.liftKaehlerDifferential : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) = 0 := by
      refine Derivation.liftKaehlerDifferential_unique _ _ (Derivation.ext fun x => ?_)
      show (b • dd.liftKaehlerDifferential) (D ℂ R x) = (0 : Ω[R⁄ℂ] →ₗ[R] R ⧸ m ^ 2) (D ℂ R x)
      rw [LinearMap.smul_apply, LinearMap.zero_apply, hL, hd, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_two]
      exact Ideal.mul_mem_mul hb (hsub x)
    intro ω
    exact LinearMap.congr_fun hz ω
  have hle : m ≤ Ig ⊔ m ^ 2 := by
    intro x hx
    set c : Fin d → ℂ := Matrix.vecMul (φ (D ℂ R x)) M⁻¹ with hcEq
    have hc : ∑ j, c j • M j = φ (D ℂ R x) := by
      have h1 : Matrix.vecMul c M = φ (D ℂ R x) := by
        rw [hcEq, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
          Matrix.vecMul_one]
      rw [← h1]
      funext l
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    set x' := x - ∑ j, c j • g j with hx'Eq
    have hx' : φ (D ℂ R x') = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hx'Eq, map_sub, map_sum, Derivation.map_smul, map_smul, hM, hc, sub_self]
    obtain ⟨k, b, ω', hb, hω⟩ := hk _ hx'
    have hx'm : x' ∈ m ^ 2 := by
      have h1 : dd.liftKaehlerDifferential (D ℂ R x') = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hω, map_sum]
        exact Finset.sum_eq_zero fun i _ => by
          rw [map_smul]
          exact hkill _ ((hmem _).mpr (hb i)) _
      have hex' : e x' = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [hx'Eq, map_sub, map_sum, map_smul, hg, (hmem x).mp hx]
      rw [hL, hd, hex', map_zero, sub_zero, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact h1
    have hsum : ∑ j, c j • g j ∈ Ig :=
      Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ (c j) (Ideal.subset_span ⟨j, rfl⟩)
    have hx : x = ∑ j, c j • g j + x' := by
      rw [hx'Eq]
      abel
    rw [hx]
    exact Submodule.add_mem_sup hsum hx'm
  have hfg : (Submodule.map (Submodule.mkQ Ig) m).FG := (IsNoetherian.noetherian m).map _
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m
    (Submodule.map (Submodule.mkQ Ig) m) hfg (by
      rw [← Submodule.map_smul'']
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨i, hi, q, hq, hiq⟩ := Submodule.mem_sup.mp (hle hx)
      refine ⟨q, ?_, ?_⟩
      · rw [pow_two, ← Ideal.smul_eq_mul] at hq
        exact hq
      · rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hiq]
        have : q - (i + q) = -i := by abel
        rw [this]
        exact Ig.neg_mem hi)
  refine ⟨r, ?_, ?_⟩
  · have h := (hmem _).mp hr1
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h
  · intro e' he' hr'
    have hIg : Ig ≤ RingHom.ker e' := Ideal.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact he' j)
    have hmk : ∀ x ∈ m, e' x = 0 := by
      intro x hx
      have h0 := hr _ (Submodule.mem_map_of_mem hx)
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at h0
      have h3 := hIg h0
      rw [RingHom.mem_ker, map_mul] at h3
      exact (mul_eq_zero.mp h3).resolve_left hr'
    ext x
    have h := hmk _ (hsub x)
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_eq_zero] at h
    exact h

private theorem ev_pull {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {c : Y ⟶ Z}
    {U : Z.Opens} {V : Y.Opens} (hV : V ≤ c ⁻¹ᵁ U) {y : CxPts s' (RingHom.id ℂ)}
    (hy : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec sZ U) :
    CxPts.ev s' (RingHom.id ℂ) V (Sec.res s' hV (appSec sZ s' c U f)) y = valR (y.1 ≫ c) U f :=
  (CxPts.ev_res hV hy _).trans (valR_comp _ _ _ _).symm

private def evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) : Sec s' V →ₐ[ℂ] ℂ :=
  { (CxPts.evHom h : Sec s' V →+* ℂ) with
    commutes' := fun a => by
      have := CxPts.ev_algX h a
      rw [CxPts.ev_eq h] at this
      exact this }

private theorem evAlg_apply {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} {y : CxPts s' (RingHom.id ℂ)}
    (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (f : Sec s' V) :
    evAlg h f = CxPts.ev s' (RingHom.id ℂ) V f y := (CxPts.ev_eq h f).symm

private theorem eq_of_evAlg {Y : Scheme.{0}} {s' : Y ⟶ Sp ℂ} {V : Y.Opens} (hV : IsAffineOpen V)
    {y y' : CxPts s' (RingHom.id ℂ)} (h : y ∈ CxPts.ptsIn s' (RingHom.id ℂ) V)
    (h' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V) (e : evAlg h' = evAlg h) : y' = y := by
  apply Subtype.ext
  rw [← specMap_valMap_fromSpec hV y'.1 h', ← specMap_valMap_fromSpec hV y.1 h]
  congr 2
  ext f
  exact congrArg (fun φ => φ f) e

private theorem isolated {Z Y : Scheme.{0}} {sZ : Z ⟶ Sp ℂ} {s' : Y ⟶ Sp ℂ} {d : ℕ} {c₁ c₂ : Y ⟶ Z}
    {h₁ : c₁ ≫ sZ = s'} {h₂ : c₂ ≫ sZ = s'} [IsLocallyNoetherian Y] (y : CxPts s' (RingHom.id ℂ))
    (hfix : y.1 ≫ c₁ = y.1 ≫ c₂) {A : Matrix (Fin d) (Fin d) ℂ}
    (hT : GlobalTheory.W1.IsTan d c₁ c₂ h₁ h₂ y A) (hdet : (1 - A).det ≠ 0) :
    ∃ W : Y.Opens, y ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y := by
  obtain ⟨U, V, hV1, hV2, t, hyV, hU, hVa, φ, hφs, hφ1, hφ2, hφk⟩ := hT
  haveI : IsNoetherianRing (Sec s' V) := IsLocallyNoetherian.component_noetherian ⟨V, hVa⟩
  let g : Fin d → Sec s' V := fun j =>
    Sec.res s' hV1 (appSec sZ s' c₁ U (t j)) - Sec.res s' hV2 (appSec sZ s' c₂ U (t j))
  have hgz : ∀ (y' : CxPts s' (RingHom.id ℂ)) (hy' : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V),
      y'.1 ≫ c₁ = y'.1 ≫ c₂ → ∀ j, evAlg hy' (g j) = 0 := by
    intro y' hy' hf j
    simp only [g, map_sub, evAlg_apply, ev_pull hV1 hy', ev_pull hV2 hy', hf, sub_self]
  have hk : ∀ ω : Ω[Sec s' V⁄ℂ], φ ω = 0 → ∃ (m : ℕ) (b : Fin m → Sec s' V)
      (ω' : Fin m → Ω[Sec s' V⁄ℂ]), (∀ i, evAlg hyV (b i) = 0) ∧ ω = ∑ i, b i • ω' i := by
    intro ω hω
    obtain ⟨m, b, ω', hb, hsum⟩ := hφk ω hω
    exact ⟨m, b, ω', fun i => by rw [evAlg_apply]; exact hb i, hsum⟩
  have hM : ∀ j, φ (D ℂ (Sec s' V) (g j)) = (1 - A) j := by
    intro j
    simp only [g, map_sub, hφ1, hφ2]
    funext l
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  obtain ⟨r, hr1, hr⟩ := iso_alg (evAlg hyV) φ hk g (hgz y hyV hfix) (1 - A) hM hdet
  refine ⟨Y.basicOpen r, ?_, ?_⟩
  · refine (CxPts.mem_ptsIn_basicOpen hyV r).mpr ?_
    rw [← evAlg_apply hyV, hr1]
    exact one_ne_zero
  · intro y' hf hy'
    have hy'V : y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) V := CxPts.ptsIn_mono (Y.basicOpen_le r) hy'
    have hne : evAlg hy'V r ≠ 0 := by
      rw [evAlg_apply]
      exact (CxPts.mem_ptsIn_basicOpen hy'V r).mp hy'
    exact eq_of_evAlg hVa hyV hy'V (hr _ (hgz y' hy'V hf) hne)

theorem fixFinite_of : FixFinite := by
  intro Z Y sZ s' d c₁ c₂ h₁ h₂ _ _ _ hiso
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian s'
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace s'
  haveI : IsNoetherian Y := {}
  set F := {y : CxPts s' (RingHom.id ℂ) | y.1 ≫ c₁ = y.1 ≫ c₂} with hF
  have hW : ∀ y : F, ∃ W : Y.Opens, y.1 ∈ CxPts.ptsIn s' (RingHom.id ℂ) W ∧
      ∀ y' : CxPts s' (RingHom.id ℂ), y'.1 ≫ c₁ = y'.1 ≫ c₂ →
        y' ∈ CxPts.ptsIn s' (RingHom.id ℂ) W → y' = y.1 := by
    intro y
    obtain ⟨A, hT, hdet⟩ := hiso y.1 y.2
    exact isolated y.1 y.2 hT hdet
  choose W hyW hW' using hW
  have hcov : (fun y : CxPts s' (RingHom.id ℂ) => (y : Sp ℂ ⟶ Y) (IsLocalRing.closedPoint ℂ)) '' F ⊆
      ⋃ i : F, (W i : Set Y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, CxPts.mem_ptsIn.mp (hyW ⟨y, hy⟩)⟩
  obtain ⟨t, ht⟩ := (TopologicalSpace.NoetherianSpace.isCompact _).elim_finite_subcover
    (fun i : F => (W i : Set Y)) (fun i => (W i).isOpen) hcov
  refine (t.finite_toSet.image Subtype.val).subset ?_
  intro y' hy'
  obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht ⟨y', hy', rfl⟩)
  exact ⟨i, hi, (hW' i y' hy' (CxPts.mem_ptsIn.mpr hmem)).symm⟩

end UpperTheory.Gal.W2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PRhoSig
noncomputable section

open NumberField
open scoped TensorProduct Matrix Classical
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace UpperTheory.Gal.W2

private theorem tens_inj (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] :
    Function.Injective (fun x : O => x ⊗ₜ[ℤ] (1 : ℤ_[p])) := by
  have hinj : Function.Injective (Algebra.linearMap ℤ ℤ_[p]) := by
    intro a b h
    exact RingHom.injective_int (algebraMap ℤ ℤ_[p]) h
  have h1 := Module.Flat.lTensor_preserves_injective_linearMap (M := O) (Algebra.linearMap ℤ ℤ_[p]) hinj
  intro x y hxy
  have h2 : x ⊗ₜ[ℤ] (1 : ℤ) = y ⊗ₜ[ℤ] (1 : ℤ) := h1 (by simpa using hxy)
  have h3 := congrArg (TensorProduct.rid ℤ O) h2
  simpa using h3

private theorem comm_of_split (p : ℕ) [Fact p.Prime] {O : Type} [Ring O] [Module.Free ℤ O] {R : Type} [CommRing R]
    {m : ℕ} (hm : m = 1) (f : (O ⊗[ℤ] ℤ_[p]) ≃+* Matrix (Fin m) (Fin m) R) (x y : O) : x * y = y * x := by
  subst hm
  apply tens_inj p
  have hc : ∀ A B : Matrix (Fin 1) (Fin 1) R, A * B = B * A := by
    intro A B
    ext i j
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp [Matrix.mul_apply, mul_comm]
  have := hc (f (x ⊗ₜ[ℤ] (1 : ℤ_[p]))) (f (y ⊗ₜ[ℤ] (1 : ℤ_[p])))
  rw [← map_mul, ← map_mul] at this
  have h2 := f.injective this
  simpa using h2

private theorem a_inj {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] : Function.Injective (algebraMap (𝓞 F) O) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro c hc
  by_contra h0
  have hI : RingHom.ker (algebraMap (𝓞 F) O) ≠ ⊥ := fun h => h0 (by
    have h1 : c ∈ RingHom.ker (algebraMap (𝓞 F) O) := hc
    rw [h] at h1
    simpa using h1)
  have hN := Ideal.absNorm_mem (RingHom.ker (algebraMap (𝓞 F) O))
  have hN0 : Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  rw [RingHom.mem_ker, map_natCast] at hN
  have h1 : (Ideal.absNorm (RingHom.ker (algebraMap (𝓞 F) O)) : ℤ) • (1 : O) = 0 := by
    rw [zsmul_one]
    exact_mod_cast hN
  rcases smul_eq_zero.mp h1 with h | h
  · exact hN0 (by exact_mod_cast h)
  · exact one_ne_zero h

private theorem a_onto {F : Type} [Field F] [NumberField F] {O : Type} [Ring O] [Algebra (𝓞 F) O] [Nontrivial O]
    [Module.Free ℤ O] [Module.Finite ℤ O] (hcomm : ∀ x y : O, x * y = y * x)
    (hc : ∀ x : O, ∃ c : 𝓞 F, ∃ e : ℤ, e ≠ 0 ∧ e • x = algebraMap (𝓞 F) O c) :
    Function.Surjective (algebraMap (𝓞 F) O) := by
  intro x
  obtain ⟨c, e, he, hx⟩ := hc x
  letI : CommRing O := { (inferInstance : Ring O) with mul_comm := hcomm }
  obtain ⟨P, hP, hPx⟩ : IsIntegral ℤ x := IsIntegral.of_finite ℤ x
  have hQ : Polynomial.eval₂ (algebraMap ℤ O) (algebraMap ℤ O e * x) (P.scaleRoots e) = 0 := by
    rw [Polynomial.scaleRoots_eval₂_mul, hPx, mul_zero]
  have hex : algebraMap ℤ O e * x = algebraMap (𝓞 F) O c := by
    rw [← hx]; simp [zsmul_eq_mul]
  have hQ2 : Polynomial.eval₂ (algebraMap ℤ (𝓞 F)) c (P.scaleRoots e) = 0 := by
    apply a_inj (O := O)
    rw [map_zero, Polynomial.hom_eval₂, ← hex, ← hQ]
    congr 1
    exact RingHom.ext_int _ _
  have hQ3 : Polynomial.eval₂ (algebraMap ℤ F) (c : F) (P.scaleRoots e) = 0 := by
    have := congrArg (algebraMap (𝓞 F) F) hQ2
    rw [map_zero, Polynomial.hom_eval₂] at this
    rw [← this]
    congr 1
  have heF : (algebraMap ℤ F e) ≠ 0 := by simpa using he
  have hcF : (c : F) = algebraMap ℤ F e * ((c : F) / algebraMap ℤ F e) := by field_simp
  rw [hcF, Polynomial.scaleRoots_eval₂_mul] at hQ3
  have hint : IsIntegral ℤ ((c : F) / algebraMap ℤ F e) :=
    ⟨P, hP, (mul_eq_zero.mp hQ3).resolve_left (pow_ne_zero _ heF)⟩
  obtain ⟨c', hc'⟩ := (IsIntegralClosure.isIntegral_iff (A := 𝓞 F)).1 hint
  refine ⟨c', ?_⟩
  have hcc : c = e • c' := by
    apply RingOfIntegers.ext
    rw [hcF, ← hc']
    simp [zsmul_eq_mul]
  have h3 : e • (algebraMap (𝓞 F) O c' - x) = 0 := by
    rw [smul_sub, hx, hcc, zsmul_eq_mul, zsmul_eq_mul]
    simp
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h he
  · exact sub_eq_zero.mp h

private theorem root_cases (tr nm : ℤ) (hd : tr ^ 2 - 4 * nm < 0) (r z : ℂ) (hr : r ^ 2 - tr * r + nm = 0)
    (hz : z ^ 2 - tr * z + nm = 0) : (starRingEnd ℂ) r ≠ r ∧ (z = r ∨ z = (starRingEnd ℂ) r) := by
  have hne : (starRingEnd ℂ) r ≠ r := by
    intro h
    obtain ⟨t, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h1 : (t : ℂ) ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by simpa using hr
    have h2 : t ^ 2 - (tr : ℝ) * t + (nm : ℝ) = 0 := by exact_mod_cast h1
    have h3 : ((tr : ℝ)) ^ 2 - 4 * (nm : ℝ) < 0 := by exact_mod_cast hd
    nlinarith [sq_nonneg (2 * t - tr)]
  refine ⟨hne, ?_⟩
  have hr' : ((starRingEnd ℂ) r) ^ 2 - tr * (starRingEnd ℂ) r + nm = 0 := by
    have := congrArg (starRingEnd ℂ) hr
    simpa using this
  have hs : r + (starRingEnd ℂ) r = tr := by
    have h1 : (r - (starRingEnd ℂ) r) * (r + (starRingEnd ℂ) r - tr) = 0 := by
      linear_combination hr - hr'
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact sub_eq_zero.mp h
  have h2 : (z - r) * (z - (starRingEnd ℂ) r) = 0 := by
    rw [← hs] at hz hr
    linear_combination hz - hr
  rcases mul_eq_zero.mp h2 with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

private theorem sum_mult {F : Type} [Field F] [NumberField F] (n : ℕ) (hn : 1 ≤ n) (t₀ : F →+* ℂ)
    (ε : (F →+* ℂ) → ℕ) (cx : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ)
    (eps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1) :
    2 * ∑ τ : F →+* ℂ, typeMult n t₀ ε τ = n * Module.finrank ℚ F := by
  have hinv : ∀ σ : F →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    ComplexEmbedding.involutive_conjugate F
  have hc0 : ComplexEmbedding.conjugate t₀ ≠ t₀ := cx t₀
  have hw : ∀ τ, typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = n := by
    intro τ
    by_cases h1 : τ = t₀
    · subst h1
      simp only [typeMult, ite_true, ite_eq_right hc0]
      omega
    by_cases h2 : τ = ComplexEmbedding.conjugate t₀
    · subst h2
      simp only [typeMult, hinv, ite_eq_right hc0, ite_true]
      omega
    have h3 : ComplexEmbedding.conjugate τ ≠ t₀ := fun h => h2 (by rw [← h, hinv])
    have h4 : ComplexEmbedding.conjugate τ ≠ ComplexEmbedding.conjugate t₀ := fun h =>
      h1 ((ComplexEmbedding.involutive_conjugate F).injective h)
    simp only [typeMult, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    rw [← Nat.mul_add, eps τ h1 h2, Nat.mul_one]
  have hs : ∑ τ : F →+* ℂ, typeMult n t₀ ε (ComplexEmbedding.conjugate τ) = ∑ τ : F →+* ℂ, typeMult n t₀ ε τ :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (ComplexEmbedding.involutive_conjugate F)) (typeMult n t₀ ε)
  have h2 : ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ + typeMult n t₀ ε (ComplexEmbedding.conjugate τ)) =
      n * Module.finrank ℚ F := by
    simp only [hw, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Embeddings.card F ℂ, mul_comm]
  rw [Finset.sum_add_distrib, hs] at h2
  omega

theorem rhoSig_of : RhoSig := by
  intro p _ D ha hm t₀ ht
  haveI := D.freeO
  haveI := D.finO
  have hd : 0 < Module.finrank ℚ D.F := Module.finrank_pos
  haveI : Nontrivial D.O := by
    apply Module.nontrivial_of_finrank_pos (R := ℤ)
    rw [D.rankO, hm]
    simpa using hd
  obtain ⟨f⟩ := D.splitP
  have hcomm : ∀ x y : D.O, x * y = y * x := comm_of_split p hm f.toRingEquiv
  have hinj : Function.Injective (algebraMap (𝓞 D.F) D.O) := a_inj
  have honto : Function.Surjective (algebraMap (𝓞 D.F) D.O) :=
    a_onto hcomm fun x => D.central x (hcomm x)
  let e : 𝓞 D.F ≃+* D.O := RingEquiv.ofBijective (algebraMap (𝓞 D.F) D.O) ⟨hinj, honto⟩
  have he : ∀ c : 𝓞 D.F, e.symm (algebraMap (𝓞 D.F) D.O c) = c := fun c => e.symm_apply_apply c
  have h0 : 0 < D.a := by omega
  have ht0 : t₀ (D.ω : D.F) = D.ρc := by
    rw [← ht ⟨0, h0⟩]
    exact D.tau_ω _
  have hroot : ∀ τ : D.F →+* ℂ, (τ (D.ω : D.F)) ^ 2 - D.tr * τ (D.ω : D.F) + D.nm = 0 := by
    intro τ
    have h1 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.tr_eq
    have h2 := congrArg (fun x : 𝓞 D.F => τ (x : D.F)) D.nm_eq
    simp only [map_add (f := _), map_mul, map_intCast] at h1 h2
    rw [← h1, ← h2]
    ring
  have hcx : ∀ τ : D.F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ := by
    intro τ h
    have hc : (InfinitePlace.mk τ).IsComplex := IsTotallyComplex.isComplex _
    exact (InfinitePlace.isComplex_mk_iff.mp hc) (ComplexEmbedding.isReal_iff.mpr h)
  have heps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ →
      epsD D τ + epsD D (ComplexEmbedding.conjugate τ) = 1 := by
    intro τ _ _
    obtain ⟨hne, hcase⟩ := root_cases D.tr D.nm D.disc_neg D.ρc (τ (D.ω : D.F)) D.ρc_root (hroot τ)
    unfold epsD
    rw [ComplexEmbedding.conjugate_coe_eq]
    rcases hcase with h | h
    · rw [h, ite_eq_left rfl, ite_eq_right hne]
    · rw [h, ite_eq_right hne, Complex.conj_conj, ite_eq_left rfl]
  have hsum : ∑ τ : D.F →+* ℂ, typeMult D.n t₀ (epsD D) τ = D.g := by
    have h2 := sum_mult D.n D.n_pos t₀ (epsD D) hcx heps
    unfold Datum.g
    rw [hm, one_mul, ← h2]
    simp
  obtain ⟨E⟩ : Nonempty (Fin D.g ≃ Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) :=
    ⟨(Fintype.equivFinOfCardEq (by simp [hsum])).symm⟩
  let ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ :=
    (Matrix.diagonalRingHom (Fin D.g) ℂ).comp
      ((RingHom.pi fun i => ((E i).1).comp (algebraMap (𝓞 D.F) D.F)).comp (e.symm : D.O →+* 𝓞 D.F))
  have hρ : ∀ c : 𝓞 D.F, ρ (algebraMap (𝓞 D.F) D.O c) = Matrix.diagonal fun i => (E i).1 (c : D.F) := by
    intro c
    simp only [ρ, RingHom.comp_apply, RingHom.coe_coe, he]
    rfl
  refine ⟨ρ, ⟨honto, fun c => ⟨D.bar c, ?_, fun τ => ?_⟩, hcx, D.n_pos, heps, fun c => ?_⟩⟩
  · show (D.star (algebraMap (𝓞 D.F) D.O c)).unop = _
    rw [D.star_F]
    rfl
  · rw [D.bar_eq, IsCMField.complexEmbedding_complexConj]
  · rw [hρ, Matrix.trace_diagonal,
      Equiv.sum_comp E (fun s : (Σ τ : D.F →+* ℂ, Fin (typeMult D.n t₀ (epsD D) τ)) => s.1 (c : D.F)),
      Fintype.sum_sigma]
    simp

end UpperTheory.Gal.W2
end
end
