module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralModelRepCoeffRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.GalD

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {c : R} (hc : c ∈ nonZeroDivisors R)
    {M M' : Matrix m n R} (h : c • M = c • M') : M = M' := by
  ext i j
  have h1 := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h1
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 h1

theorem map_smul_hom {R S : Type} [CommRing R] [CommRing S] {m n : Type} (f : R →+* S) (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

theorem mul_eq_smul_comm {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    {X X' : Matrix n n R} {c : R} (hc : c ∈ nonZeroDivisors R) (h : X * X' = c • (1 : Matrix n n R)) :
    X' * X = c • (1 : Matrix n n R) := by
  have hdet : X.det ∈ nonZeroDivisors R := by
    have h4 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h4
    have h5 : X.det * X'.det ∈ nonZeroDivisors R := h4 ▸ pow_mem hc _
    exact (mul_mem_nonZeroDivisors.1 h5).1
  have h2 : X * (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, h, smul_mul_assoc, Matrix.one_mul, mul_smul_comm, Matrix.mul_one,
      sub_self]
  have h3 : X.det • (X' * X - c • (1 : Matrix n n R)) = 0 := by
    rw [← Matrix.one_mul (X' * X - c • (1 : Matrix n n R)), ← smul_mul_assoc, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h2, Matrix.mul_zero]
  rw [← smul_zero X.det] at h3
  exact sub_eq_zero.1 (smul_cancel hdet h3)

theorem key {R : Type} [CommRing R] {n : Type} [Fintype n] {P YG Ya U UG Bi Bg ε : Matrix n n R}
    {L e ge t gt : R} {N : ℕ} (hc : L * ge ^ (2 * N) * e ^ (2 * N) ∈ nonZeroDivisors R)
    (hY : U * Bi = (L * e ^ (2 * N)) • Ya) (hYG : UG * Bg = (L * ge ^ (2 * N)) • YG)
    (hgal : (e * t) ^ N • (P * UG) = (ge * gt) ^ N • U) (hR : ge ^ N • (Bi * ε) = e ^ N • Bg) :
    t ^ N • (P * YG) = gt ^ N • (Ya * ε) := by
  refine smul_cancel hc ?_
  calc (L * ge ^ (2 * N) * e ^ (2 * N)) • (t ^ N • (P * YG))
      = (e ^ N * (e * t) ^ N) • (P * ((L * ge ^ (2 * N)) • YG)) := by
        rw [smul_smul, mul_smul_comm, smul_smul]; congr 1; ring
    _ = (e ^ N * (e * t) ^ N) • (P * (UG * Bg)) := by rw [hYG]
    _ = e ^ N • (((e * t) ^ N • (P * UG)) * Bg) := by rw [smul_mul_assoc, Matrix.mul_assoc, smul_smul]
    _ = e ^ N • (((ge * gt) ^ N • U) * Bg) := by rw [hgal]
    _ = (ge * gt) ^ N • (U * (e ^ N • Bg)) := by
        rw [smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul, mul_comm]
    _ = (ge * gt) ^ N • (U * (ge ^ N • (Bi * ε))) := by rw [hR]
    _ = ((ge * gt) ^ N * ge ^ N) • ((U * Bi) * ε) := by rw [mul_smul_comm, smul_smul, Matrix.mul_assoc]
    _ = ((ge * gt) ^ N * ge ^ N) • (((L * e ^ (2 * N)) • Ya) * ε) := by rw [hY]
    _ = (L * ge ^ (2 * N) * e ^ (2 * N)) • (gt ^ N • (Ya * ε)) := by
        rw [smul_mul_assoc, smul_smul, smul_smul]; congr 1; ring

end GlobalTheory.BSP.GalD


open GlobalTheory.BSP.GalD in
theorem GlobalTheory.BSP.Height.rel_gal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  intro l _ K bk d ρ τ s ht _hτ g ε hrel
  have hl0 : (0 : ℝ≥0) < l := Nat.cast_pos.2 (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := NNReal.rpow_pos hl0
  have h0 : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  have h1 : ‖toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev X))‖ ≤ bk.ρ₀ :=
    (GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).1
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev h0 with hi_def
  set G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map (Per.σA (g : GQ l)) h1 with hG_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  have hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G := isDiscMap_map _ _
  have hFg : IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf ((ainfHom K g).comp bk.ι)) (G.comp i) :=
    ⟨fun a => by
      change G (i (toDisc l X bk.ρ₀ a)) = toDisc l (bk.ev X) bk.ρ₀ (Per.σA (g : GQ l) (bk.ev a))
      rw [hi.ext, hG.ext], fun x => (hG.norm_le _).trans (hi.norm_le x)⟩
  have hR : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ s.N • (ht.bas.map i * ε) =
      bk.iA (bk.ev bk.E) ^ s.N • ht.bas.map (G.comp i) := hrel i (G.comp i) hi hFg
  have hGA : ∀ a, G (bk.iA a) = bk.iA (Per.σA (g : GQ l) a) := hG.ext

  have hbi : ht.bas.map i = s.X.map bk.iS * ht.Z.map i := by
    rw [Height.bas, Matrix.map_mul, Matrix.map_map]
    congr 1
    ext a b
    exact hi.ext _
  have hbg : ht.bas.map (G.comp i) = (s.X.map bk.iS).map G * (ht.Z.map i).map G := by
    rw [← Matrix.map_mul, ← hbi, Matrix.map_map]; rfl

  obtain ⟨ιb, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have he : bk.iA (bk.ev bk.E) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ιb tb).2.1
  have hL : ((l : bk.DA bk.ρ₀) ^ s.c₂) ∈ nonZeroDivisors (bk.DA bk.ρ₀) :=
    ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow _).mem_nonZeroDivisors
  obtain ⟨w, hw⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk (ainfObj K) bk.ι ((ainfHom K g).comp bk.ι)).2.1
  have hw' : bk.ev bk.E * (show Ainf l from (w : (ainfObj K).A)) = Per.σA (g : GQ l) (bk.ev bk.E) := hw
  have hwu : IsUnit (bk.iA (show Ainf l from (w : (ainfObj K).A))) := w.isUnit.map bk.iA
  have hge : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
    rw [← hw', map_mul]
    exact mul_mem he hwu.mem_nonZeroDivisors

  have hXX1 : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, map_smul_hom, Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hXX := mul_eq_smul_comm (mul_mem hL (pow_mem he _)) hXX1
  set U := s.W * s.X'.map bk.iS with hU
  have hY : U * (s.X.map bk.iS * ht.Z.map i) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (bk.ev bk.E) ^ (2 * s.N)) • ht.Y.map bk.iA := by
    rw [hU, Matrix.mul_assoc, ← Matrix.mul_assoc (s.X'.map bk.iS), hXX, smul_mul_assoc, Matrix.one_mul,
      mul_smul_comm, ht.W_mul i hi]
  have hYG : U.map G * ((s.X.map bk.iS).map G * (ht.Z.map i).map G) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA (Per.σA (g : GQ l) (bk.ev bk.E)) ^ (2 * s.N)) •
        (ht.Y.map bk.iA).map G := by
    have := congrArg (fun M => Matrix.map M G) hY
    simp only [Matrix.map_mul, map_smul_hom] at this
    rw [this, map_mul, map_pow, map_pow, map_natCast, hGA]
  have hgal := s.gal g G hG
  rw [← hU, map_mul, map_mul] at hgal
  have hgoal : (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) =
      (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (ht.Y.map bk.iA).map G := by
    rw [Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.map_map]
    congr 1
    ext a b
    exact (hGA _).symm
  rw [hgoal]
  rw [hbg] at hR
  rw [hbi] at hR
  simp only [map_mul] at hgal
  exact key (mul_mem (mul_mem hL (pow_mem hge _)) (pow_mem he _)) hY hYG hgal hR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelGaloisComparisonMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_galois_comparison_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (g : ↥(GK K)) (ε : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), ht.Rel (B := ainfObj K) (BK.hf bk.ι X) bk.ι ((ainfHom K g).comp bk.ι) ε → bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * ht.Y.map (Per.σA (g : GQ l))).map bk.iA) = bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (ht.Y.map bk.iA * ε) := by
  first | exact @GlobalTheory.BSP.Height.rel_gal | exact GlobalTheory.BSP.Height.rel_gal | (intros; apply GlobalTheory.BSP.Height.rel_gal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPower
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

namespace GlobalTheory.CrysPrism.Decay

theorem pow_add_mul_range {M R : Type} [AddCommGroup M] [CommRing R] (f : M →+ R)
    (hm : ∀ x y : M, ∃ z, f z = f x * f y) (x y : M) (c n : ℕ) :
    ∃ p g : M, f p = f x ^ (n + 1) ∧ (f x + c * f y) ^ (n + 1) = f x ^ (n + 1) + c * f g := by
  induction n with
  | zero => exact ⟨x, y, by simp, by simp⟩
  | succ n ih =>
    obtain ⟨p, g, hp, hg⟩ := ih
    obtain ⟨p', hp'⟩ := hm p x
    obtain ⟨z1, h1⟩ := hm p y
    obtain ⟨z2, h2⟩ := hm g x
    obtain ⟨z3, h3⟩ := hm g y
    refine ⟨p', z1 + z2 + c • z3, by rw [hp', hp]; ring, ?_⟩
    rw [pow_succ, hg, map_add (f := _), map_add (f := _), map_nsmul, h1, h2, h3, hp, nsmul_eq_mul]
    ring

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

def ofWHom : (ℕ × ℕ → Wq l a) →+ (ZMod a → K⟦X⟧⟦X⟧) :=
  AddMonoidHom.mk' (ofW t K e) fun x y => by
    funext τ
    ext i n
    simp only [Pi.add_apply, map_add (f := _), coeff_ofW, add_div]

theorem ofWHom_apply (w : ℕ × ℕ → Wq l a) : ofWHom t K e w = ofW t K e w := rfl

theorem eq_zero_of_coeff [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (w : ℕ × ℕ → Wq l a) (i n : ℕ) (h : coeff n (coeff i (ofW t K e w 0)) = 0) : w (i, n) = 0 := by
  rw [coeff_ofW, div_eq_zero_iff] at h
  have h2 : (dpDen e i n : K) ≠ 0 := Nat.cast_ne_zero.2 (dpDen_pos e i n).ne'
  apply hinj 0
  simpa using h.resolve_right h2

theorem ofWHom_injective [CharZero K]
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) :
    Function.Injective (ofWHom t K e) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro w hw
  funext ⟨i, n⟩
  apply eq_zero_of_coeff t K e hinj
  rw [← ofWHom_apply, hw]
  simp

theorem box_cofinite (M : ℕ) : ∀ᶠ p : ℕ × ℕ in cofinite, M < p.1 ∨ M < p.2 := by
  rw [Filter.eventually_cofinite]
  refine ((Set.finite_Iic M).prod (Set.finite_Iic M)).subset ?_
  rintro ⟨i, n⟩ h
  simp only [Set.mem_setOf_eq, not_or, not_lt] at h
  exact h

end GlobalTheory.CrysPrism.Decay

namespace GlobalTheory.CrysPrism
open Decay

theorem frob_keeps_decay (l : ℕ) [hl : Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O]
    [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hinj : ∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c))
    (hmul : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e)
    (hQ : ∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂)
    (hsupp : ∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) →
      ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n →
        coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0)
    (w : ℕ × ℕ → Wq l a) (hw : LTo0 l w) (v b : ℕ × ℕ → Wq l a)
    (hv : frob2 φ₂ (ofW t K e w) = ofW t K e v)
    (hb : frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b) :
    LTo0 l v ∧ LTo0 l b := by
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 hl.out.ne_zero
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := natCast_ne_zero_ps (natCast_ne_zero_ps hl0)
  have hI := ofWHom_injective t K e hinj
  have key : ∀ r : ℕ, ∀ᶠ p in cofinite, (l : Wq l a) ^ r ∣ v p ∧ (l : Wq l a) ^ r ∣ b p := by
    intro r
    have hS := hw (r + 1)
    rw [Filter.eventually_cofinite] at hS
    obtain ⟨⟨N1, N2⟩, hN⟩ := hS.bddAbove
    let w1 : ℕ × ℕ → Wq l a := fun p => if (l : Wq l a) ^ (r + 1) ∣ w p then 0 else w p
    have hex : ∀ p, ∃ c, w p = w1 p + (l ^ (r + 1) : ℕ) • c := by
      intro p
      by_cases h : (l : Wq l a) ^ (r + 1) ∣ w p
      · obtain ⟨c, hc⟩ := id h
        refine ⟨c, ?_⟩
        simp only [w1, if_pos h]
        simp [hc]
      · exact ⟨0, by simp only [w1, if_neg h]; simp⟩
    choose w2 hw2 using hex
    have hw12 : w = w1 + (l ^ (r + 1) : ℕ) • w2 := funext hw2
    have hw1 : ∀ i n, max N1 N2 < i ∨ max N1 N2 < n → w1 (i, n) = 0 := by
      intro i n h
      by_cases h' : (l : Wq l a) ^ (r + 1) ∣ w (i, n)
      · simp only [w1, if_pos h']
      · have h3 : (i, n) ≤ (N1, N2) := hN h'
        obtain ⟨h4, h5⟩ := h3
        simp only at h4 h5
        omega
    obtain ⟨M, hM⟩ := hsupp _ w1 hw1
    obtain ⟨-, ⟨v1, hv1⟩, _, ⟨b1, rfl⟩, hb1⟩ := hQ _ ⟨w1, rfl⟩
    obtain ⟨-, ⟨v2, hv2⟩, -⟩ := hQ _ ⟨w2, rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, l = k + 1 := Nat.exists_eq_succ_of_ne_zero hl.out.ne_zero
    obtain ⟨-, g, -, hg⟩ := pow_add_mul_range (ofWHom t K e)
      (fun x y => hmul _ ⟨x, rfl⟩ _ ⟨y, rfl⟩) w1 w2 (l ^ (r + 1)) k
    rw [← hk] at hg
    have hF : ofW t K e w = ofW t K e w1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e w2 := by
      rw [← ofWHom_apply, hw12, map_add (f := _), map_nsmul, nsmul_eq_mul]; rfl
    have hφ : frob2 φ₂ (ofW t K e w) =
        ofW t K e v1 + ((l ^ (r + 1) : ℕ) : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e v2 := by
      rw [hF, map_add (f := _), map_mul, map_natCast, hv1, hv2]
    have e1 : v = v1 + (l ^ (r + 1) : ℕ) • v2 := by
      apply hI
      rw [map_add (f := _), map_nsmul, nsmul_eq_mul, ofWHom_apply, ← hv, hφ]; rfl
    have e2 : b = b1 + (l ^ r : ℕ) • (v2 - g) := by
      apply hI
      rw [map_add (f := _), map_nsmul, map_sub, nsmul_eq_mul, ← sub_eq_zero]
      apply tf_pi hl2
      simp only [ofWHom_apply] at hg ⊢
      rw [← hF] at hg
      rw [← hv1] at hb1
      push_cast at hg hφ ⊢
      linear_combination hφ - hb - hg + hb1
    filter_upwards [box_cofinite M] with ⟨i, n⟩ hp
    obtain ⟨m1, m2⟩ := hM 0 i n hp
    have z1 : v1 (i, n) = 0 := eq_zero_of_coeff t K e hinj v1 i n (by rw [hv1]; exact m1)
    have z2 : b1 (i, n) = 0 := by
      apply eq_zero_of_coeff t K e hinj
      rw [hb1, ← nsmul_eq_mul, Pi.add_apply, map_add (f := _), map_add (f := _), m2, zero_add, Pi.smul_apply, map_nsmul, map_nsmul,
        nsmul_eq_mul] at m1
      exact (mul_eq_zero.1 m1).resolve_left hl0
    constructor
    · rw [e1]
      simp only [Pi.add_apply, Pi.smul_apply, z1, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow _ (Nat.le_succ r)) _
    · rw [e2]
      simp only [Pi.add_apply, Pi.smul_apply, z2, zero_add, nsmul_eq_mul, Nat.cast_pow]
      exact Dvd.intro _ rfl
  exact ⟨fun r => (key r).mono fun _ h => h.1, fun r => (key r).mono fun _ h => h.2⟩

end GlobalTheory.CrysPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPowerStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → (∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂) → (∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0) → ∀ w : ℕ × ℕ → Wq l a, LTo0 l w → ∀ v b : ℕ × ℕ → Wq l a, frob2 φ₂ (ofW t K e w) = ofW t K e v → frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b → LTo0 l v ∧ LTo0 l b := by
  first | exact @GlobalTheory.CrysPrism.frob_keeps_decay | exact GlobalTheory.CrysPrism.frob_keeps_decay | (intros; apply GlobalTheory.CrysPrism.frob_keeps_decay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveMaxUnramifiedSubfieldAlgebraMap
noncomputable section

namespace GlobalTheory.TopSteps.FinSummandDim

open Module TensorProduct
open GlobalTheory.AdmLoc GlobalTheory.TopSteps GlobalTheory.TopSteps.FinSummand Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N

section General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace Qp] [TopologicalSpace LL]

theorem h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) : H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ = ⊥ := by
  obtain ⟨_, _, _⟩ := hO.1
  refine invariants_stableLattice_mod_irreducible_eq_bot (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hlam ?_
  change (coefRep (latRep (twLattice Γ.T₀.L Γ.χ₁⁻¹)) (O ⧸ Ideal.span {Γ.lam})).invariants = ⊥
  rw [latRep_twLattice]
  exact h0

theorem finrank_h0V_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hlam : Irreducible Γ.lam)
    (h0 : (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.resRep Γ).invariants = ⊥) :
    finrank LL ↥(H0V (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) = 0 := by
  rw [h0V_tw hO Γ hχ hlam h0, finrank_bot]

theorem isCompl_tw (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hfin : Module.Finite O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ)) :
    ∃ C : Submodule O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) C := by
  obtain ⟨_, _, _⟩ := hO.1
  exact exists_isCompl_of_saturated _ (h1fT_saturated PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L)

theorem finrank_tw [CompactSpace G] (hO : GoodO (Qp := Qp) LL O) (Γ : GalData G Qp LL O)
    (hχ : Continuous fun g => algebraMap O LL (Γ.χ₁⁻¹ g)) (hT : IsOpen (Γ.T₀.L.T : Set Γ.T₀.V)) :
    finrank O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf PD Γ) = finrank LL (FiniteCohomology PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).ρ) := by
  obtain ⟨_, _, _⟩ := hO.1
  exact finrank_h1fT PD (twLat Γ.T₀ Γ.χ₁⁻¹ hχ).L hT

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P)

theorem cont_inv (hC : S.CrysCalc) : Continuous fun g => algebraMap S.O ↥S.LL.1 (S.Γ.χ₁⁻¹ g) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2.1

abbrev tw (hC : S.CrysCalc) : LocLat S.G ℚ_[l] ↥S.LL.1 S.O := twLat S.Γ.T₀ S.Γ.χ₁⁻¹ (cont_inv S hC)

theorem tw_crysWith (hC : S.CrysCalc) :
    CrysWith (P.PD S.K) S.emb (tw S hC).ρ (fun i => (S.D.U i).map (· + -S.D.w i)) := by
  obtain ⟨-, ⟨-, hρ, hχ, -⟩, -⟩ := S.hyp
  have h1 := (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁ S.D.w hρ hχ).2
  exact (hC.2.1 S.Γ.T₀ S.D.U S.Γ.χ₁⁻¹ _ hρ h1).1

set_option synthInstance.maxHeartbeats 100000 in
theorem tw_finrank_h0V (hC : S.CrysCalc) (hV : S.Vanish) : finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) = 0 := by
  obtain ⟨⟨-, -, -, -, -, hlam⟩, -⟩ := S.hyp
  exact finrank_h0V_tw (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hlam hV.1

theorem exists_isCompl (hC : S.CrysCalc) (hH : S.FreeH) :
    ∃ C : Submodule S.O (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.HH S.Γ), IsCompl (GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) C :=
  isCompl_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC) hH.1.2.1

theorem finrank_hf (hC : S.CrysCalc) :
    finrank S.O ↥(GlobalTheory.IndefiniteRowSideFullHecke.InvariantsVanishing.Hf (P.PD S.K) S.Γ) = finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) :=
  haveI := GlobalTheory.BlochKatoIntegralScalars.compactSpace_GK S.K
  finrank_tw (P.PD S.K) (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ (cont_inv S hC)
    (GlobalTheory.Cyc.locLat_isOpen (GlobalTheory.LocalIntegers.good_integers l S.LL).1 S.Γ.T₀)

theorem sum_card_neg :
    ∑ i, Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) = S.D.dsum := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Multiset.filter_map, Multiset.card_map, TopData.d]
  exact congrArg _ (Multiset.filter_congr fun u _ => by simp)

theorem bijective_maxUnramifiedSubfield_algebraMap : Function.Bijective (algebraMap ↥(K0 S.K) ↥S.K.1) := by
  obtain ⟨⟨-, hA, -⟩, -⟩ := S.hyp
  exact ⟨RingHom.injective _, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩

theorem fSummand_of_finrank (hC : S.CrysCalc) (hH : S.FreeH)
    (hd : finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) = S.D.dsum) : S.FSummand :=
  ⟨exists_isCompl S hC hH, (finrank_hf S hC).trans hd⟩

set_option synthInstance.maxHeartbeats 100000 in
theorem fSummand_of_dim (hC : S.CrysCalc) (hV : S.Vanish) (hH : S.FreeH)
    (hd : (finrank ↥S.LL.1 (FiniteCohomology (P.PD S.K) (tw S hC).ρ) : ℤ) = (finrank ↥S.LL.1 ↥(H0V (tw S hC).ρ) : ℤ) +
      ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ)) : S.FSummand := by
  refine fSummand_of_finrank S hC hH ?_
  have h0 := tw_finrank_h0V S hC hV
  have h1 : ∑ i, (Multiset.card (((S.D.U i).map (· + -S.D.w i)).filter (· < 0)) : ℤ) = (S.D.dsum : ℤ) := by
    rw [← sum_card_neg S, Nat.cast_sum]
  have key : ∀ (a b c : ℕ) (s : ℤ), (a : ℤ) = (b : ℤ) + s → b = 0 → s = (c : ℤ) → a = c := by
    intro a b c s h h' h''
    omega
  exact key _ _ _ _ hd h0 h1

end GlobalTheory.TopSteps.FinSummandDim
end
end

noncomputable section

namespace GlobalTheory.TopSteps.FinSummandJumps

open Module

theorem finsum_count_neg (U : Multiset ℤ) (m : ℤ → ℤ) (h : ∀ a, m a = (U.count a : ℤ)) :
    ∑ᶠ (a : ℤ) (_ : a < 0), m a = (Multiset.card (U.filter (· < 0)) : ℤ) := by
  classical
  have h1 : ∀ a : ℤ, ∑ᶠ (_ : a < 0), m a = (((U.filter (· < 0)).count a : ℕ) : ℤ) := fun a => by
    rw [finsum_eq_if, h, Multiset.count_filter]
    split_ifs <;> simp
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := (U.filter (· < 0)).toFinset),
    ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  intro a ha
  have ha' : (U.filter (· < 0)).count a ≠ 0 := fun h0 => ha (by simp only [h0, Nat.cast_zero])
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha'))

section General

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem finsum_multV_neg {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (U : ZMod n → Multiset ℤ)
    (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    ∑ᶠ (τ : K →ₐ[Qp] LL), ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => finsum_count_neg (U i) _ (hU i (e i) (he i))

end General


open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.TopSteps.FinSummandDim in
theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), tableLineDegreeTwo.BlochKatoJumpDimension (P.PD S.K) (LL := ↥S.LL.1) (O := S.O) (IK S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P S hB hC hV hH
  obtain ⟨⟨-, -, -, hemb, -⟩, -⟩ := S.hyp
  have : IsTopologicalAddGroup (tw S hC).V := IsModuleTopology.topologicalAddGroup ↥S.LL.1 (tw S hC).V
  have h := hB.1 (tw S hC).V (tw S hC).ρ (tw S hC).cont (tw_crysWith S hC).1
  exact fSummand_of_dim S hC hV hH (h.trans (congrArg _
    (finsum_multV_neg (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandJumps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedVariablePowerFrobeniusCongrPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedVariablePowerFrobeniusCongrPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.GoodX

theorem pow_factorial_dvd (i m : ℕ) : i.factorial ^ m ∣ (m * i).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem mul_pow_factorial_dvd (l i : ℕ) (hl : l ≠ 0) (hi : i ≠ 0) :
    i.factorial ^ l * l ∣ (l * i).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have h1 : i ≤ (m + 1) * i := by nlinarith
  have h2 := Nat.choose_mul_factorial_mul_factorial h1
  have h3 : (m + 1) * i - i = m * i := by rw [Nat.succ_mul]; omega
  rw [h3, Nat.choose_mul_right hi] at h2
  obtain ⟨c, hc⟩ := pow_factorial_dvd i m
  refine ⟨((m + 1) * i - 1).choose (i - 1) * c, ?_⟩
  rw [Nat.succ_eq_add_one, ← h2, hc]; ring

theorem exists_padic (l : ℕ) [hl : Fact l.Prime] (i : ℕ) (hi : i ≠ 0) :
    ∃ d : ℤ_[l], (i.factorial : ℤ_[l]) * d = (l : ℤ_[l]) ^ (i - 1) := by
  have hv : multiplicity l i.factorial ≤ i - 1 := by
    have h := hl.out.sub_one_mul_multiplicity_factorial (n := i)
    have h2 := hl.out.two_le
    have h3 : (l.digits i).sum ≠ 0 := by
      intro h0
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hi
      exact Nat.getLast_digit_ne_zero l hi (List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne))
    have h4 : 1 * multiplicity l i.factorial ≤ (l - 1) * multiplicity l i.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨s, hs⟩ : l ^ multiplicity l i.factorial ∣ i.factorial := (by rw [← Nat.padicValNat_def]; exact _root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hs' : ¬ l ∣ s := by
    intro h
    refine pow_succ_multiplicity_not_dvd (p := l) (Nat.factorial_ne_zero i) ?_
    rw [pow_succ]
    conv_rhs => rw [hs]
    exact Nat.mul_dvd_mul_left _ h
  have hu : IsUnit (s : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hs' ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (s : ℤ)).1 (by simpa using h)
    exact_mod_cast this
  obtain ⟨s', hs2⟩ := hu.exists_right_inv
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hv
  refine ⟨(l : ℤ_[l]) ^ k * s', ?_⟩
  have h5 : (i.factorial : ℤ_[l]) = (l : ℤ_[l]) ^ multiplicity l i.factorial * s := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hs
  rw [hk, pow_add]
  linear_combination ((l : ℤ_[l]) ^ k * s') * h5 + ((l : ℤ_[l]) ^ multiplicity l i.factorial * (l : ℤ_[l]) ^ k) * hs2

theorem abstract {R : Type} [CommRing R] (htf : ∀ n : ℕ, n ≠ 0 → ∀ x : R, (n : R) * x = 0 → x = 0)
    (S : Subring R) (φ : R →+* R) (l : ℕ) (hl : l ≠ 0) (u x : R) (xs : ℕ → R)
    (hxs : ∀ k : ℕ, (k.factorial : R) * xs k = x ^ k) (hu : u ∈ S) (hxS : ∀ k, xs k ∈ S)
    (hφ : φ x = (u + x) ^ l - u ^ l) (i : ℕ) (hi : i ≠ 0) (d : R) (hd : d ∈ S)
    (hdi : (i.factorial : R) * d = (l : R) ^ (i - 1)) :
    φ (xs i) ∈ S ∧ ∃ B ∈ S, φ (xs i) = xs i ^ l + (l : R) * B := by
  obtain ⟨Y, hY, hP⟩ : ∃ Y ∈ S, φ x = (l : R) * Y := by
    refine ⟨∑ m ∈ Finset.range l, ((l - 1).descFactorial m : R) * u ^ (l - (m + 1)) * xs (m + 1), ?_, ?_⟩
    · exact S.sum_mem fun m _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hu _)) (hxS _)
    · rw [hφ, add_comm u x, add_pow, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        add_sub_cancel_right]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h : (m + 1).factorial * l.choose (m + 1) = l * (l - 1).descFactorial m := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
        exact Nat.succ_descFactorial_succ n m
      have h' : ((m + 1).factorial : R) * (l.choose (m + 1) : R) = (l : R) * ((l - 1).descFactorial m : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) h
      rw [← hxs]
      linear_combination (u ^ (l - (m + 1)) * xs (m + 1)) * h'
  have h1 : φ (xs i) = (l : R) * (d * Y ^ i) := by
    rw [← sub_eq_zero]
    apply htf _ (Nat.factorial_ne_zero i)
    have h := congrArg φ (hxs i)
    rw [map_mul, map_natCast, map_pow, hP, mul_pow] at h
    have h2 : (l : R) ^ i = l * (l : R) ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2] at h
    linear_combination h - ((l : R) * Y ^ i) * hdi
  obtain ⟨c, hc⟩ := mul_pow_factorial_dvd l i hl hi
  have h2 : xs i ^ l = (l : R) * (c * xs (l * i)) := by
    rw [← sub_eq_zero]
    apply htf _ (pow_ne_zero l (Nat.factorial_ne_zero i))
    have h := congrArg (· ^ l) (hxs i)
    have h3 := hxs (l * i)
    rw [hc] at h3
    simp only [mul_pow, ← pow_mul] at h
    rw [mul_comm i l] at h
    push_cast at h3 ⊢
    linear_combination h - h3
  have hm : d * Y ^ i ∈ S := S.mul_mem hd (S.pow_mem hY _)
  refine ⟨h1 ▸ S.mul_mem (natCast_mem S _) hm, d * Y ^ i - c * xs (l * i),
    S.sub_mem hm (S.mul_mem (natCast_mem S _) (hxS _)), ?_⟩
  rw [h1, h2]; ring

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

theorem mono_mem (c : Wq l a) (i n : ℕ) :
    (fun τ => C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i :
      ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (i, n) then c else 0, funext fun τ => ?_⟩
  ext j m
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, mul_one, coeff_C_mul, coeff_X_pow]
    by_cases hm : m = n
    · subst hm; simp
    · simp [hm]
  · simp [hj]

theorem add_mem {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  refine ⟨v + w, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.add_apply, map_add (f := _), coeff_ofW, add_div]

theorem neg_mem {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨-v, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.neg_apply, map_neg, coeff_ofW, neg_div]

theorem cstW_mem (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  convert mono_mem t K e c 0 0 using 1
  funext τ
  simp [cstW, dpDen]

theorem xFam_mem (i : ℕ) : xFam a K i ∈ QSet t K e := by
  convert mono_mem t K e 1 i 0 using 1
  funext τ
  simp [xFam, dpDen]

theorem uFam_mem : uFam a K ∈ QSet t K e := by
  convert mono_mem t K e 1 0 1 using 1
  funext τ
  have h : (1 / e).factorial = 1 := by
    rw [Nat.factorial_eq_one]; exact Nat.div_le_self _ _
  simp [uFam, dpDen, h]

def qSub (h : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) : Subring (ZMod a → K⟦X⟧⟦X⟧) where
  carrier := QSet t K e
  mul_mem' := fun hx hy => h _ hx _ hy
  one_mem' := by
    convert cstW_mem t K e 1 using 1
    funext τ; simp [cstW]
  add_mem' := add_mem t K e
  zero_mem' := by
    convert cstW_mem t K e 0 using 1
    funext τ; simp [cstW]
  neg_mem' := neg_mem t K e

end Q

theorem xFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → ∀ i : ℕ, xFam a K i ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX hmul i
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨xFam_mem t K e i, ?_⟩
  by_cases hi : i = 0
  · subst hi
    have h : xFam a K 0 = 1 := by funext τ; simp [xFam]
    rw [h, map_one]
    exact ⟨(qSub t K e hmul).one_mem, 0, (qSub t K e hmul).zero_mem, by simp⟩
  obtain ⟨d, hd⟩ := exists_padic l i hi
  refine abstract (fun n hn x hx => tf_pi (natCast_ne_zero_ps (natCast_ne_zero_ps (Nat.cast_ne_zero.2 hn))) x hx)
    (qSub t K e hmul) (frob2 φ₂) l hl.out.ne_zero (uFam a K) (fun _ => X) (xFam a K) (fun k => ?_)
    (uFam_mem t K e) (xFam_mem t K e) ?_ i hi (cstW t K (algebraMap ℤ_[l] _ d)) (cstW_mem t K e _) ?_
  · funext τ
    have h : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, xFam]
    rw [← mul_assoc, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_natCast (C : K →+* K⟦X⟧), ← map_mul, ← map_mul,
      mul_inv_cancel₀ h]
    simp
  · funext τ
    change φ₂ X = (C X + X) ^ l - C X ^ l
    rw [hX, map_pow]
  · funext τ
    have h := congrArg (fun z => (C (C (algebraMap O K (algebraMap ℤ_[l] O z))) : K⟦X⟧⟦X⟧)) hd
    simp only [map_mul, map_natCast, map_pow] at h
    simpa [cstW] using h

end GlobalTheory.CrysPrism.GoodX
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DividedVariablePowerFrobeniusCongrPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedVariablePower_frobenius_congr_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → ∀ i : ℕ, xFam a K i ∈ GoodSet t e φ₂ := by
  first | exact @GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet | exact GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet | (intros; apply GlobalTheory.CrysPrism.GoodX.xFam_mem_GoodSet <;> assumption)
end
end
