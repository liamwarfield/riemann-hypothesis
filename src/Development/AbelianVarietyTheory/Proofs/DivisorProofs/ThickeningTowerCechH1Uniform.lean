module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPow
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg

theorem eval₂_eq_of_sub_mem_of_coeff_mem_pow {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (I : Ideal R) (e : ℕ) (hbot : (I ^ (e + 1)).map φ = ⊥) (F : MvPolynomial σ R)
    (hF : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) (a b : σ → B) (hab : ∀ l, a l - b l ∈ I.map φ) :
    MvPolynomial.eval₂ φ a F = MvPolynomial.eval₂ φ b F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h1 : (∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l ∈ I.map φ := by
    rw [← Ideal.Quotient.eq]
    simp only [map_prod, map_pow]
    exact Finset.prod_congr rfl fun l _ => by rw [Ideal.Quotient.eq.2 (hab l)]
  have h2 : φ (AddMonoidAlgebra.coeff F m) * ((∏ l ∈ m.support, a l ^ m l) - ∏ l ∈ m.support, b l ^ m l) ∈
      (I ^ (e + 1)).map φ := by
    rw [pow_succ, Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hF m)) h1
  rw [hbot, Ideal.mem_bot, mul_sub, sub_eq_zero] at h2
  exact h2

theorem eval₂_mem_map_of_coeff_mem {R B σ : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (J : Ideal R) (F : MvPolynomial σ R) (hF : ∀ m, AddMonoidAlgebra.coeff F m ∈ J) (a : σ → B) :
    MvPolynomial.eval₂ φ a F ∈ J.map φ := by
  rw [MvPolynomial.eval₂_eq]
  exact Ideal.sum_mem _ fun m _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m))

theorem Charts.ev_change (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hpb : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (n : ℕ) (C : Charts I Y β n)
    (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R) (hF : F.IsHomogeneous d)
    (hc : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) (i j : Fin (n + 1)) :
    C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧
      rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) =
        rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d *
          rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  obtain ⟨hbot, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hpb n C
  obtain ⟨-, hself, hcoc⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C
  have h1 : C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) :=
    eval₂_mem_map_of_coeff_mem _ _ F hc _
  refine ⟨h1, ?_, ?_⟩
  · have h := Ideal.mul_mem_mul (hself e i) h1
    have h' : (C.ρ e i i - 1) * C.ev e i F ∈ towerIdeal Y e (I ^ (e + 1)) (C.D e i) := by
      have hm : towerIdeal Y e (I ^ (e + 1)) (C.D e i) =
          towerIdeal Y e I (C.D e i) * towerIdeal Y e (I ^ e) (C.D e i) := by
        unfold towerIdeal
        rw [← Ideal.map_mul, ← pow_succ']
      rw [hm]
      exact h
    rw [hbot, Ideal.mem_bot, sub_mul, one_mul, sub_eq_zero] at h'
    exact h'
  · have hi : (rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    have hj : (rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j)).comp
        (GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e j)) =
        GlobalTheory.AbLaw.cst ((Y e).hom ≫ thick R I e) (C.D e i ⊓ C.D e j) :=
      RingHom.ext fun r => rs_cst _ _ r
    simp only [Charts.ev, MvPolynomial.coe_eval₂Hom]
    rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hi, hj, ← eval₂_scale _ _ _ hF]
    exact eval₂_eq_of_sub_mem_of_coeff_mem_pow _ I e (hbot e _) F hc _ _ fun l => hcoc e i j l

end GlobalTheory.FormalAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormChartChangeCoeffIdealPowStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j, C.ev e i F ∈ towerIdeal Y e (I ^ e) (C.D e i) ∧ C.ρ e i i * C.ev e i F = C.ev e i F ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ d * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (C.ev e j F) := by
  first | exact @GlobalTheory.FormalAlg.Charts.ev_change | exact GlobalTheory.FormalAlg.Charts.ev_change | (intros; apply GlobalTheory.FormalAlg.Charts.ev_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormKilledByPowerOfTripleChartProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormKilledByPowerOfTripleChartProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.TripleKill

theorem rs_rs {X : Scheme} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    rs X h2 (rs X h1 x) = rs X (h2.trans h1) x := by
  simp only [rs]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem ev_triple_kill : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j l, rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ev e i F) = 0 → ∃ L : ℕ, ∀ m, C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ L * F) = 0 := by
  intro R _ I Y β hpb n C e d F hF hI i j l h0
  have hlev := (GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hpb n C).1
  have htr := GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hpb n C e d F hF hI
  have key : ∀ m, ∃ L : ℕ, (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ L * C.ev e m F = 0 := by
    intro m
    apply exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen _ (C.aff e m)
    have hb : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) =
        (C.D e m ⊓ C.D e i) ⊓ (C.D e m ⊓ C.D e j) ⊓ (C.D e m ⊓ C.D e l) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, hlev, hlev, hlev]
    have hW1 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e m ⊓ C.D e i :=
      hb.le.trans (inf_le_left.trans inf_le_left)
    have hW2 : (Y e).left.basicOpen (C.ρ e m i * C.ρ e m j * C.ρ e m l) ≤ C.D e i ⊓ C.D e j ⊓ C.D e l :=
      hb.le.trans (le_inf (le_inf (inf_le_left.trans (inf_le_left.trans inf_le_right))
        (inf_le_left.trans (inf_le_right.trans inf_le_right))) (inf_le_right.trans inf_le_right))
    change rs (Y e).left ((Y e).left.basicOpen_le _) (C.ev e m F) = 0
    have h1 := (htr m i).2.2
    have h2 : rs (Y e).left hW1 (rs (Y e).left (inf_le_left : C.D e m ⊓ C.D e i ≤ C.D e m) (C.ev e m F)) = 0 := by
      rw [h1, map_mul, rs_rs, ← rs_rs (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) hW2, h0,
        map_zero, mul_zero]
    rw [rs_rs] at h2
    exact h2
  choose Lf hL using key
  refine ⟨Finset.univ.sup Lf, fun m => ?_⟩
  have hle : Lf m ≤ Finset.univ.sup Lf := Finset.le_sup (Finset.mem_univ m)
  have hev : C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ Finset.univ.sup Lf * F) =
      (C.ρ e m i * C.ρ e m j * C.ρ e m l) ^ Finset.univ.sup Lf * C.ev e m F := by
    simp [Charts.ev, map_mul, map_pow]
  rw [hev, ← Nat.sub_add_cancel hle, pow_add (C.ρ e m i * C.ρ e m j * C.ρ e m l), mul_assoc, hL m, mul_zero]

end GlobalTheory.FormalAlg.TripleKill
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousFormKilledByPowerOfTripleChartProductStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousForm_killed_by_power_of_tripleChart_product : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e d : ℕ) (F : MvPolynomial (Fin (n + 1)) R), F.IsHomogeneous d → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → ∀ i j l, rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ev e i F) = 0 → ∃ L : ℕ, ∀ m, C.ev e m ((MvPolynomial.X i * MvPolynomial.X j * MvPolynomial.X l) ^ L * F) = 0 := by
  first | exact @GlobalTheory.FormalAlg.TripleKill.ev_triple_kill | exact GlobalTheory.FormalAlg.TripleKill.ev_triple_kill | (intros; apply GlobalTheory.FormalAlg.TripleKill.ev_triple_kill <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormOfOverlapIdealPowThickening
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormOfOverlapIdealPowThickening
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg.JFrac

open MvPolynomial

theorem exists_rs_eq_pow_mul {X : Scheme} {U V : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hV : X.basicOpen f = V) (h : V ≤ U) (b : Γ(X, V)) :
    ∃ (M : ℕ) (a : Γ(X, U)), rs X h a = rs X h f ^ M * b := by
  subst hV
  obtain ⟨M, a, ha⟩ :=
    exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated X U hU.isCompact hU.isQuasiSeparated f b
  exact ⟨M, a, ha⟩

theorem exists_form : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (i j : Fin (n + 1)) (c : Γ((Y e).left, C.D e i ⊓ C.D e j)), c ∈ towerIdeal Y e (I ^ e) _ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ k : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (k + 2 * N) ∧ (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ N * c := by
  intro R _ I Y β hP n C e i j c hc
  obtain ⟨hbasic, -, -⟩ := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hP n C
  obtain ⟨-, hsurj⟩ := GlobalTheory.T.thickeningTower_liftedRatios_generate_surjective R I Y β hP n C
  have hVU : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hX : ∀ l, C.ev e i (X l) = C.ρ e i l := fun l => by simp [Charts.ev]
  let J : Ideal (MvPolynomial (Fin (n + 1)) R) := Ideal.map MvPolynomial.C (I ^ e)
  let S : Ideal Γ((Y e).left, C.D e i ⊓ C.D e j) :=
    { carrier := {c | ∃ N₁ : ℕ, ∃ G ∈ J,
        rs (Y e).left hVU (C.ev e i G) = rs (Y e).left hVU (C.ρ e i j) ^ N₁ * c}
      add_mem' := by
        rintro a b ⟨N₁, G, hG, h1⟩ ⟨N₂, G', hG', h2⟩
        refine ⟨N₁ + N₂, X j ^ N₂ * G + X j ^ N₁ * G',
          J.add_mem (J.mul_mem_left _ hG) (J.mul_mem_left _ hG'), ?_⟩
        simp only [map_add (f := _), map_mul, map_pow, hX, h1, h2]
        ring
      zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro b a ⟨N₁, G, hG, h1⟩
        obtain ⟨M, a', ha'⟩ := exists_rs_eq_pow_mul (C.aff e i) (C.ρ e i j) (hbasic e i j) hVU b
        obtain ⟨H, rfl⟩ := hsurj e i a'
        refine ⟨M + N₁, H * G, J.mul_mem_left _ hG, ?_⟩
        simp only [map_mul, ha', h1, smul_eq_mul]
        ring }
  have hcS : c ∈ S := by
    refine (Ideal.map_le_iff_le_comap.2 (fun r hr => ?_)) hc
    refine ⟨0, MvPolynomial.C r, Ideal.mem_map_of_mem _ hr, ?_⟩
    simp [Charts.ev, rs_cst]
  obtain ⟨N₁, G, hG, hN₁⟩ := hcS
  have hGc : ∀ d, homogeneousComponent d G ∈ J := fun d => by
    refine MvPolynomial.mem_map_C_iff.2 fun m => ?_
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact MvPolynomial.mem_map_C_iff.1 hG m
    · exact (I ^ e).zero_mem
  have hfix : ∀ d t, C.ρ e i i ^ t * C.ev e i (homogeneousComponent d G) =
      C.ev e i (homogeneousComponent d G) := fun d t => by
    have h1 := (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hP n C e d (homogeneousComponent d G)
      (homogeneousComponent_isHomogeneous d G) (MvPolynomial.mem_map_C_iff.1 (hGc d)) i i).2.1
    induction t with
    | zero => simp
    | succ t ih => rw [pow_succ (C.ρ e i i) t, mul_assoc, h1, ih]
  refine ⟨N₁ + G.totalDegree, fun N hN k => ?_⟩
  refine ⟨X j ^ (N - N₁) * ∑ d ∈ Finset.range (G.totalDegree + 1),
      X i ^ (k + N + N₁ - d) * homogeneousComponent d G, ?_, ?_, ?_⟩
  · have hdeg : k + 2 * N = (N - N₁) + (k + N + N₁) := by omega
    rw [hdeg]
    refine (isHomogeneous_X_pow _ _).mul (IsHomogeneous.sum _ _ _ fun d hd => ?_)
    have hd' : d ≤ k + N + N₁ := by
      have := Finset.mem_range.1 hd
      omega
    have := (isHomogeneous_X_pow i (k + N + N₁ - d)).mul (homogeneousComponent_isHomogeneous d G)
    rwa [Nat.sub_add_cancel hd'] at this
  · exact MvPolynomial.mem_map_C_iff.1
      (J.mul_mem_left _ (J.sum_mem fun d _ => J.mul_mem_left _ (hGc d)))
  · have hsum : C.ev e i (∑ d ∈ Finset.range (G.totalDegree + 1),
        X i ^ (k + N + N₁ - d) * homogeneousComponent d G) = C.ev e i G := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← sum_homogeneousComponent G, map_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, map_pow, hX, hfix]
    rw [map_mul, hsum, map_mul, hN₁, map_pow, map_pow, hX, ← mul_assoc, ← pow_add,
      Nat.sub_add_cancel (by omega : N₁ ≤ N)]

end GlobalTheory.FormalAlg.JFrac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormOfOverlapIdealPowThickeningStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_form_of_overlap_ideal_pow_thickening : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (i j : Fin (n + 1)) (c : Γ((Y e).left, C.D e i ⊓ C.D e j)), c ∈ towerIdeal Y e (I ^ e) _ → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ k : ℕ, ∃ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous (k + 2 * N) ∧ (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) ∧ rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ev e i F) = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ N * c := by
  first | exact @GlobalTheory.FormalAlg.JFrac.exists_form | exact GlobalTheory.FormalAlg.JFrac.exists_form | (intros; apply GlobalTheory.FormalAlg.JFrac.exists_form <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedRatiosEvalIdealMulEqZeroSucc
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedRatiosEvalIdealMulEqZeroSucc
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false

namespace GlobalTheory.FormalAlg.JStep

theorem appLE_cst {R : Type} [CommRing R] {X X' : Scheme.{0}} (g : X ⟶ X') (f : X' ⟶ Spec (CommRingCat.of R))
    (U' : X'.Opens) (U : X.Opens) (h : U ≤ g ⁻¹ᵁ U') (r : R) :
    (g.appLE U' U h).hom (AbLaw.cst f U' r) = AbLaw.cst (g ≫ f) U r := by
  simp only [AbLaw.cst, RingHom.comp_apply, rs]
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ← CommRingCat.comp_apply (g.appTop)]
  congr 1

theorem cst_pow_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst (p ≫ thick R I e) V a = 0 := by
  rw [thick, cst_comp_spec, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]

theorem ev_succ_C_mul_eq_zero : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)), a ∈ I → C.ev e i F = 0 → C.ev (e + 1) i (MvPolynomial.C a * F) = 0 := by
  intro R _ I Y β hpb n C e a F i ha hF
  have hsq := (GlobalTheory.T.isPullback_thick_tower_squares R I Y β hpb).1 e
  have hk := (GlobalTheory.T.baseChange_quotient_closedImmersion_idealSheaf R (I ^ (e + 1)) (Y (e + 1)).left (Y e).left ((Y (e + 1)).hom ≫ thick R I (e + 1))
    (β e) (Y e).hom hsq).2.2 (C.D (e + 1) i) (C.aff (e + 1) i)
  have hw : β e ≫ (Y (e + 1)).hom ≫ thick R I (e + 1) = (Y e).hom ≫ thick R I e := by
    rw [← Category.assoc, (hpb e).w, Category.assoc, thickTrans_comp]

  have hev : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom (C.ev (e + 1) i F) = C.ev e i F := by
    have hcomp : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom.comp (C.ev (e + 1) i) = C.ev e i := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [Charts.ev, appLE_cst, hw]
      · intro j
        simp [Charts.ev, C.ρ_pull]
    exact RingHom.congr_fun hcomp F

  have hx : C.ev (e + 1) i F ∈ RingHom.ker ((β e).app (C.D (e + 1) i)).hom := by
    rw [RingHom.mem_ker]
    have h2 : ((β e).appLE (C.D (e + 1) i) (C.D e i) (C.pre e i).ge).hom (C.ev (e + 1) i F) =
        rs (Y e).left (C.pre e i).ge (((β e).app (C.D (e + 1) i)).hom (C.ev (e + 1) i F)) := rfl
    rw [hev, hF] at h2
    have h3 := congrArg (rs (Y e).left (C.pre e i).le) h2
    rw [map_zero, rs_rs, rs_self] at h3
    exact h3.symm
  rw [hk.2] at hx
  rw [map_mul, Charts.ev, MvPolynomial.eval₂Hom_C]
  have hm : AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i) a * C.ev (e + 1) i F ∈
      (I * I ^ (e + 1)).map (AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i)) := by
    rw [Ideal.map_mul]
    exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ ha) hx
  have hbot : (I * I ^ (e + 1)).map (AbLaw.cst ((Y (e + 1)).hom ≫ thick R I (e + 1)) (C.D (e + 1) i)) = ⊥ := by
    refine le_bot_iff.1 (Ideal.map_le_iff_le_comap.2 fun r hr => ?_)
    rw [← pow_succ'] at hr
    simp only [Ideal.mem_comap, Ideal.mem_bot]
    exact cst_pow_eq_zero I (e + 1) (Y (e + 1)).hom _ hr
  rw [hbot] at hm
  exact (Ideal.mem_bot).1 hm

end GlobalTheory.FormalAlg.JStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftedRatiosEvalIdealMulEqZeroSuccStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ : ∀ (R : Type) [CommRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∀ (e : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R) (i : Fin (n + 1)), a ∈ I → C.ev e i F = 0 → C.ev (e + 1) i (MvPolynomial.C a * F) = 0 := by
  first | exact @GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | exact GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero | (intros; apply GlobalTheory.FormalAlg.JStep.ev_succ_C_mul_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdea
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdea
open MvPolynomial DirectSum

namespace GlobalTheory

theorem cocycle_all_pairs_of_lt {Q : Type*} [CommRing Q] {ι : Type*} [LinearOrder ι]
    (x : ι → Q) (f : ι → ι → Q) (g : ι → Q) (N N' : ℕ)
    (hcoc : ∀ i j l, ∃ L : ℕ, (x i * x j * x l) ^ L * (x l ^ N * f i j + x i ^ N * f j l - x j ^ N * f i l) = 0)
    (hlt : ∀ i j, i < j → ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0)
    (i j : ι) : ∃ L : ℕ, (x i * x j) ^ L *
      ((x i * x j) ^ N' * f i j - (x i * x j) ^ N * (x j ^ N' * g i - x i ^ N' * g j)) = 0 := by
  obtain ⟨L₃, h₃⟩ := hcoc i i i
  have h₃' : x i ^ (3 * L₃ + N) * f i i = 0 := by linear_combination h₃
  rcases lt_trichotomy i j with h | rfl | h
  · exact hlt i j h
  · exact ⟨3 * L₃ + N, by linear_combination (x i ^ (3 * L₃ + N + 2 * N')) * h₃'⟩
  · obtain ⟨L₁, h₁⟩ := hlt j i h
    obtain ⟨L₂, h₂⟩ := hcoc i j i
    have hs : x i ^ (2 * L₂ + 3 * L₃ + 2 * N) * x j ^ L₂ * (f i j + f j i) = 0 := by
      linear_combination (x i ^ (3 * L₃ + N)) * h₂ + ((x i ^ 2 * x j) ^ L₂ * x j ^ N) * h₃'
    refine ⟨3 * L₂ + 3 * L₃ + 2 * N + L₁, ?_⟩
    linear_combination (x i ^ L₂ * x j ^ (2 * L₂ + 3 * L₃ + 2 * N) * (x i * x j) ^ L₁ *
      (x i * x j) ^ N') * hs - (x i * x j) ^ (3 * L₂ + 3 * L₃ + 2 * N) * h₁

theorem exists_triple_of_card_eq_three {ι : Type*} [LinearOrder ι] {t : Finset ι}
    (ht : t.card = 3) : ∃ i j l, i < j ∧ j < l ∧ t = {i, j, l} := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.1 ht
  rcases lt_or_gt_of_ne hab with h1 | h1 <;> rcases lt_or_gt_of_ne hac with h2 | h2 <;>
    rcases lt_or_gt_of_ne hbc with h3 | h3
  all_goals first
    | exact ⟨a, b, c, by assumption, by assumption, rfl⟩
    | exact ⟨a, b, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨a, c, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, a, c, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨b, c, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, a, b, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | exact ⟨c, b, a, by assumption, by assumption, by ext; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto⟩
    | (exfalso; order)

theorem Cube.d_two_apply_triple {ι : Type} [LinearOrder ι] {R : Type*} [Ring R]
    (A : Cube ι R) (x : Cube.Term A 2) {i j l : ι} (hij : i < j) (hjl : j < l) :
    Cube.d A 2 x ⟨{i, j, l}, by rw [Finset.card_eq_three]; exact ⟨i, j, l, hij.ne, (hij.trans hjl).ne, hjl.ne, rfl⟩⟩ =
      Cube.res A (by intro k; simp; tauto) (x ⟨{j, l}, Finset.card_pair hjl.ne⟩) -
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, l}, Finset.card_pair (hij.trans hjl).ne⟩) +
        Cube.res A (by intro k; simp; tauto) (x ⟨{i, j}, Finset.card_pair hij.ne⟩) := by
  have hil := hij.trans hjl
  rw [Cube.d_apply_extend, Finset.sum_insert (by simp [hij.ne, hil.ne]), Finset.sum_pair hjl.ne,
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hjl.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hil.ne),
    ← Cube.extend_apply_of_eq A x (Finset.card_pair hij.ne)]
  have e1 : ({i, j, l} : Finset ι).erase i = {j, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne', hil.ne']
  have e2 : ({i, j, l} : Finset ι).erase j = {i, l} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hij.ne, hjl.ne']
  have e3 : ({i, j, l} : Finset ι).erase l = {i, j} := by
    ext k; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hk, h | h | h⟩ <;> first | exact absurd h hk | simp [h]
    · rintro (rfl | rfl) <;> simp [hil.ne, hjl.ne]
  have s1 : cubeSign ({i, j, l} : Finset ι) i = 1 :=
    cubeSign_eq_one_of_forall_le (by simp [hij.le, hil.le])
  have s2 : cubeSign ({i, j, l} : Finset ι) j = -1 := by
    have := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hij
    rw [e1, cubeSign_eq_one_of_forall_le (by simp [hjl.le])] at this
    omega
  have s3 : cubeSign ({i, j, l} : Finset ι) l = 1 := by
    have a1 := cubeSign_erase_of_lt (t := {i, j, l}) (by simp) hil
    rw [e1] at a1
    have a2 := cubeSign_erase_of_lt (t := {j, l}) (by simp) hjl
    rw [Finset.erase_insert (by simp [hjl.ne]), cubeSign_singleton] at a2
    omega
  rw [Cube.res_congr A _ e1 _ (by intro k; simp; tauto), Cube.res_congr A _ e2 _ (by intro k; simp; tauto),
    Cube.res_congr A _ e3 _ (by intro k; simp; tauto), s1, s2, s3]
  simp only [one_smul, neg_smul]
  abel

section GrCubeVal
variable {ι : Type} {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
  [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
  {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] {n : ℤ}

abbrev grCubeVal {s : Finset ι} (z : (grCube ι ℳ n).obj s) :
    LocalizedModule.Away (xProd R s) M :=
  Subtype.val (p := fun w => w ∈ homLoc ℳ s n) z

theorem grCubeVal_add {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a + b) = grCubeVal a + grCubeVal b := rfl

theorem grCubeVal_sub {s : Finset ι} (a b : (grCube ι ℳ n).obj s) :
    grCubeVal (a - b) = grCubeVal a - grCubeVal b := rfl

theorem grCubeVal_zero {s : Finset ι} : grCubeVal (0 : (grCube ι ℳ n).obj s) = 0 := rfl

theorem grCubeVal_injective {s : Finset ι} :
    Function.Injective (grCubeVal : (grCube ι ℳ n).obj s → _) := fun _ _ h => Subtype.ext h

theorem grCubeVal_res {s t : Finset ι} (h : s ⊆ t) (z : (grCube ι ℳ n).obj s) :
    grCubeVal (Cube.res (grCube ι ℳ n) h z) = locRes X M h (grCubeVal z) := rfl

end GrCubeVal

theorem exists_coboundary_lt {ι : Type} [LinearOrder ι] [Fintype ι] {A : Type} [CommRing A]
    (J : Ideal (MvPolynomial ι A)) (d : ℕ)
    (hex : Function.Exact (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 1)
      (Cube.d (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2))
    (N : ℕ) (F : ι → ι → MvPolynomial ι A) (hF : ∀ i j, (F i j).IsHomogeneous (d + 2 * N))
    (hcoc : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j * X l) ^ L *
      (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) :
    ∃ (N' : ℕ) (G : ι → MvPolynomial ι A), (∀ i, (G i).IsHomogeneous (d + N')) ∧
      ∀ i j, i < j → ∃ L : ℕ, ((X i : MvPolynomial ι A) * X j) ^ L *
        ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  classical
  have hne : ∀ s : {s : Finset ι // s.card = 2}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; norm_num)
  let x : Cube.Term (grCube ι (grQuot (polyGrading ι A) J) (d : ℤ)) 2 := fun s =>
    ⟨awayFrac _ (xProd A s.1) N
        (Submodule.Quotient.mk (p := J) (F (s.1.min' (hne s)) (s.1.max' (hne s)))),
      awayFrac_mem_homLoc ⟨_, mem_polyGrading_natCast.2 (hF _ _), rfl⟩
        (by rw [s.2]; push_cast; ring)⟩
  have hmin : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).min' hn = i :=
    fun i j h hn => le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by simp [h.le]))
  have hmax : ∀ i j, i < j → ∀ hn : ({i, j} : Finset ι).Nonempty, ({i, j} : Finset ι).max' hn = j :=
    fun i j h hn => le_antisymm (Finset.max'_le _ _ _ (by simp [h.le])) (Finset.le_max' _ _ (by simp))
  have hx : ∀ i j (h : i < j), grCubeVal (x ⟨{i, j}, Finset.card_pair h.ne⟩) =
      awayFrac _ (xProd A {i, j}) N (Submodule.Quotient.mk (p := J) (F i j)) := by
    intro i j h
    show awayFrac _ _ N _ = _
    rw [hmin i j h, hmax i j h]
  have hdx : Cube.d _ 2 x = 0 := by
    funext ⟨t, ht⟩
    obtain ⟨i, j, l, hij, hjl, rfl⟩ := exists_triple_of_card_eq_three ht
    rw [Cube.d_two_apply_triple _ x hij hjl]
    have hil := hij.trans hjl
    apply grCubeVal_injective
    rw [grCubeVal_add, grCubeVal_sub, grCubeVal_res, grCubeVal_res, grCubeVal_res, hx j l hjl,
      hx i l hil, hx i j hij, Pi.zero_apply, grCubeVal_zero]
    have hP : (∏ k ∈ ({i, j, l} : Finset ι), (X k : MvPolynomial ι A)) = X i * X j * X l := by
      rw [Finset.prod_insert (by simp [hij.ne, hil.ne]), Finset.prod_pair hjl.ne, mul_assoc]
    rw [locRes_awayFrac X _ (c := X i) (by rw [hP, Finset.prod_pair hjl.ne]; ring),
      locRes_awayFrac X _ (c := X j) (by rw [hP, Finset.prod_pair hil.ne]; ring),
      locRes_awayFrac X _ (c := X l) (by rw [hP, Finset.prod_pair hij.ne]; ring),
      ← map_sub, ← map_add, awayFrac_eq_zero_iff]
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hL' := Ideal.Quotient.eq_zero_iff_mem.2 hL
    rw [hP]
    simp only [map_mul, map_pow, map_add (f := _), map_sub] at hL'
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow]
    linear_combination hL'
  obtain ⟨y, hy⟩ := (hex x).1 hdx
  have hk := fun i : ι => exists_awayFrac_of_mem_homLoc (grQuot (polyGrading ι A) J)
    (Subtype.property (p := fun w => w ∈ homLoc (grQuot (polyGrading ι A) J) {i} (d : ℤ))
      (y ⟨{i}, Finset.card_singleton i⟩))
  choose k₀ hk₀ using hk
  set N' := Finset.univ.sup k₀ with hN'
  choose m hm hmeq using fun i => hk₀ i N' (Finset.le_sup (Finset.mem_univ i))
  have hmeq' : ∀ i, grCubeVal (y ⟨{i}, Finset.card_singleton i⟩) =
      awayFrac _ (xProd A {i}) N' (m i) := fun i => (hmeq i).symm
  choose g hg hgm using fun i => mem_grQuot.1 (hm i)
  refine ⟨N', fun i => -g i, fun i => ?_, fun i j h => ?_⟩
  · refine mem_polyGrading_natCast.1 ?_
    have := neg_mem (hg i)
    simp only [Finset.card_singleton] at this
    convert this using 2
    push_cast
    ring
  · have e := congrArg grCubeVal (congrFun hy ⟨{i, j}, Finset.card_pair h.ne⟩)
    rw [Cube.d_one_apply_pair _ _ h, grCubeVal_sub, grCubeVal_res, grCubeVal_res, hx i j h,
      hmeq' i, hmeq' j, ← hgm i, ← hgm j,
      locRes_awayFrac X _ (c := X i) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]),
      locRes_awayFrac X _ (c := X j) (by rw [Finset.prod_pair h.ne, Finset.prod_singleton]; ring),
      ← map_sub, awayFrac_eq_iff] at e
    obtain ⟨l, hl⟩ := e
    rw [Finset.prod_pair h.ne] at hl
    simp only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.mk_eq_mk, map_mul,
      map_pow, mul_sub] at hl
    refine ⟨l, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simp only [map_mul, map_pow, map_sub, map_neg]
    linear_combination (exp := 1) -hl

theorem exists_coboundary_of_cocycle_homogeneous : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  intro A _ _ n J hJ
  classical
  have hJh : (J : Submodule (MvPolynomial (Fin (n + 1)) A) (MvPolynomial (Fin (n + 1)) A)).IsHomogeneous
      (polyGrading (Fin (n + 1)) A) := by
    have e : J = Submodule.span (MvPolynomial (Fin (n + 1)) A)
        {g | ∃ F ∈ J, ∃ k : ℕ, g = homogeneousComponent k F} := by
      apply le_antisymm
      · intro F hF
        rw [← sum_homogeneousComponent F]
        exact Submodule.sum_mem _ fun k _ => Submodule.subset_span ⟨F, hF, k, rfl⟩
      · rw [Submodule.span_le]
        rintro _ ⟨F, hF, k, rfl⟩
        exact hJ F hF k
    rw [e]
    exact isHomogeneous_span_gr _ (by
      rintro _ ⟨F, _, k, rfl⟩
      exact ⟨k, mem_polyGrading_natCast.2 (homogeneousComponent_isHomogeneous k F)⟩)
  letI := grQuotDecomposition (polyGrading (Fin (n + 1)) A) hJh
  obtain ⟨n₀, h₀⟩ := cubeComplex_grCube_exactAt_of_finite (Fin (n + 1)) A
    (MvPolynomial (Fin (n + 1)) A ⧸ J) (grQuot (polyGrading (Fin (n + 1)) A) J) inferInstance
  refine ⟨n₀.toNat, fun d hd N F hF hcoc => ?_⟩
  have hex := (cubeComplex_exactAt_succ_iff _ 1).1 (h₀ d (by omega) 2)
  obtain ⟨N', G, hG, hlt⟩ := exists_coboundary_lt J d hex N F hF hcoc
  refine ⟨N', G, hG, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := cocycle_all_pairs_of_lt (fun i => Ideal.Quotient.mk J (X i))
    (fun i j => Ideal.Quotient.mk J (F i j)) (fun i => Ideal.Quotient.mk J (G i)) N N'
    (fun i j l => (hcoc i j l).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add (f := _)] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    (fun i j h => (hlt i j h).imp fun L hL => by
      simpa only [map_mul, map_pow, map_sub, map_add (f := _)] using Ideal.Quotient.eq_zero_iff_mem.2 hL)
    i j
  exact ⟨L, Ideal.Quotient.eq_zero_iff_mem.1 (by simpa only [map_mul, map_pow, map_sub] using hL)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfFractionCocycleHomogeneousIdeaStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (G i).IsHomogeneous (d + N')) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J := by
  first | exact @GlobalTheory.exists_coboundary_of_cocycle_homogeneous | exact GlobalTheory.exists_coboundary_of_cocycle_homogeneous | (intros; apply GlobalTheory.exists_coboundary_of_cocycle_homogeneous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocycles
open MvPolynomial

namespace GlobalTheory.UniformCocycle

variable {R : Type} [CommRing R] {σ : Type}

noncomputable def proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    MvPolynomial σ R :=
  ∑ m ∈ P.support, monomial m (((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e)

theorem coeff_proj (I : Ideal R) (e : ℕ) (P : MvPolynomial σ (reesAlgebra I)) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (proj I e P) m = ((AddMonoidAlgebra.coeff P m : reesAlgebra I) : Polynomial R).coeff e := by
  classical
  simp only [proj, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    simp [h]

theorem proj_add (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P + Q) = proj I e P + proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_sub (I : Ideal R) (e : ℕ) (P Q : MvPolynomial σ (reesAlgebra I)) :
    proj I e (P - Q) = proj I e P - proj I e Q := by
  ext m; simp [coeff_proj]

theorem proj_X_mul (I : Ideal R) (e : ℕ) (i : σ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i * P) = X i * proj I e P := by
  classical
  ext m
  rw [coeff_proj, coeff_X_mul', coeff_X_mul']
  split_ifs <;> simp [coeff_proj]

theorem proj_Xpow_mul (I : Ideal R) (e : ℕ) (i : σ) (k : ℕ) (P : MvPolynomial σ (reesAlgebra I)) :
    proj I e (X i ^ k * P) = X i ^ k * proj I e P := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_assoc, proj_X_mul, ih, ← mul_assoc, ← pow_succ']


open Classical in
noncomputable def liftCoeff (I : Ideal R) (e : ℕ) (r : R) : reesAlgebra I :=
  if h : r ∈ I ^ e then ⟨Polynomial.monomial e r, reesAlgebra.monomial_mem.mpr h⟩ else 0

theorem liftCoeff_zero (I : Ideal R) (e : ℕ) : liftCoeff I e 0 = 0 := by
  unfold liftCoeff
  rw [dite_eq_left (zero_mem _)]
  apply Subtype.ext; simp

noncomputable def liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) :
    MvPolynomial σ (reesAlgebra I) :=
  ∑ m ∈ F.support, monomial m (liftCoeff I e (AddMonoidAlgebra.coeff F m))

theorem coeff_liftE (I : Ideal R) (e : ℕ) (F : MvPolynomial σ R) (m : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (liftE I e F) m = liftCoeff I e (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [liftE, coeff_sum, coeff_monomial, Finset.sum_ite_eq', mem_support_iff]
  split_ifs with h
  · rfl
  · rw [not_not] at h
    rw [h, liftCoeff_zero]

theorem proj_liftE {I : Ideal R} {e : ℕ} {F : MvPolynomial σ R} (h : ∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e)
    (e' : ℕ) : proj I e' (liftE I e F) = if e' = e then F else 0 := by
  ext m
  rw [coeff_proj, coeff_liftE, liftCoeff, dite_eq_left (h m)]
  simp only [Polynomial.coeff_monomial]
  by_cases h1 : e' = e
  · subst h1; simp
  · rw [Finsupp.single_eq_of_ne h1, ite_eq_right h1]
    simp

theorem isHomogeneous_liftE {I : Ideal R} {e t : ℕ} {F : MvPolynomial σ R}
    (hF : F.IsHomogeneous t) : (liftE I e F).IsHomogeneous t := by
  intro m hm
  apply hF
  intro h0
  apply hm
  rw [coeff_liftE, h0, liftCoeff_zero]

theorem isHomogeneous_proj {I : Ideal R} {e t : ℕ} {P : MvPolynomial σ (reesAlgebra I)}
    (hP : P.IsHomogeneous t) : (proj I e P).IsHomogeneous t := by
  intro m hm
  apply hP
  intro h0
  apply hm
  rw [coeff_proj, h0]
  simp

end GlobalTheory.UniformCocycle

namespace GlobalTheory


open UniformCocycle in
theorem uniformSerre_cocycle : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  open UniformCocycle in
  intro R _ _ I n J hJ
  obtain ⟨𝔞, h𝔞h, h𝔞⟩ := GlobalTheory.T.exists_homogeneous_ideal_over_reesAlgebra R I n J hJ
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.exists_coboundary_of_fraction_cocycle_homogeneous_ideal (reesAlgebra I) n 𝔞 h𝔞h
  refine ⟨d₀, fun d hd e N F hFh hFc hcoc => ?_⟩
  have hF'h : ∀ i j, (liftE I e (F i j)).IsHomogeneous (d + 2 * N) :=
    fun i j => isHomogeneous_liftE (hFh i j)
  have hF'p : ∀ e' i j, proj I e' (liftE I e (F i j)) = if e' = e then F i j else 0 :=
    fun e' i j => proj_liftE (hFc i j) e'
  have hcoc' : ∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l)) ∈ 𝔞 := by
    intro i j l
    obtain ⟨L, hL⟩ := hcoc i j l
    refine ⟨L, ?_⟩
    have hh := ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).mul (isHomogeneous_X _ l)).pow L).mul
      ((((isHomogeneous_X_pow l N).mul (hF'h i j)).add ((isHomogeneous_X_pow i N).mul (hF'h j l))).sub
        ((isHomogeneous_X_pow j N).mul (hF'h i l)))
    rw [h𝔞 _ _ hh]
    intro e' G hG
    have hGe : G = proj I e' (((X i : MvPolynomial (Fin (n + 1)) (reesAlgebra I)) * X j * X l) ^ L *
      (X l ^ N * liftE I e (F i j) + X i ^ N * liftE I e (F j l) - X j ^ N * liftE I e (F i l))) := by
      ext m; rw [hG, coeff_proj]
    rw [hGe]
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p]
    by_cases he : e' = e
    · subst he
      simp only [↓reduceIte]
      simpa only [mul_pow, mul_assoc] using hL
    · simp [he]
  obtain ⟨N', G', hG'h, hG'⟩ := hd₀ d hd N (fun i j => liftE I e (F i j)) hF'h hcoc'
  refine ⟨N', fun i => proj I e (G' i), fun i => isHomogeneous_proj (hG'h i), fun i m => ?_, fun i j => ?_⟩
  · rw [coeff_proj]
    exact (mem_reesAlgebra_iff I _).mp (AddMonoidAlgebra.coeff (G' i) m).2 e
  · obtain ⟨L, hL⟩ := hG' i j
    refine ⟨L, ?_⟩
    have h2 : (1 + 1) * N + (N' + (d + N')) = (1 + 1) * N' + (d + 2 * N) := by ring
    have hh := (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow L).mul
      ((((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N').mul (hF'h i j) |>.sub
        (h2 ▸ (((isHomogeneous_X _ i).mul (isHomogeneous_X _ j)).pow N).mul
          (((isHomogeneous_X_pow j N').mul (hG'h i)).sub ((isHomogeneous_X_pow i N').mul (hG'h j)))))
    rw [h𝔞 _ _ hh] at hL
    have := hL e (proj I e _) (fun m => coeff_proj I e _ m)
    simp only [mul_pow, mul_assoc, proj_add, proj_sub, proj_Xpow_mul, hF'p, ↓reduceIte] at this
    simpa only [mul_pow, mul_assoc] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSerreVanishingCechCocyclesStatement
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_serre_vanishing_cech_cocycles : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (n : ℕ) (J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R)), (∀ (e t : ℕ) (a : R) (F : MvPolynomial (Fin (n + 1)) R), a ∈ I → F.IsHomogeneous t → (∀ m, AddMonoidAlgebra.coeff F m ∈ I ^ e) → F ∈ J e → C a * F ∈ J (e + 1)) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ e : ℕ, ∀ (N : ℕ) (F : Fin (n + 1) → Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i j, (F i j).IsHomogeneous (d + 2 * N)) → (∀ i j m, AddMonoidAlgebra.coeff (F i j) m ∈ I ^ e) → (∀ i j l, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j * X l) ^ L * (X l ^ N * F i j + X i ^ N * F j l - X j ^ N * F i l) ∈ J e) → ∃ (N' : ℕ) (G : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R), (∀ i, (G i).IsHomogeneous (d + N')) ∧ (∀ i m, AddMonoidAlgebra.coeff (G i) m ∈ I ^ e) ∧ ∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) R) * X j) ^ L * ((X i * X j) ^ N' * F i j - (X i * X j) ^ N * (X j ^ N' * G i - X i ^ N' * G j)) ∈ J e := by
  first | exact @GlobalTheory.uniformSerre_cocycle | exact GlobalTheory.uniformSerre_cocycle | (intros; apply GlobalTheory.uniformSerre_cocycle <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.FormalAlg GlobalTheory.Degen.FormalEmb

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg.TowerH1
variable {R : Type} [CommRing R] {I : Ideal R}
  {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}

theorem cst_eq_zero (e : ℕ) (V : (Y e).left.Opens) {a : R} (ha : a ∈ I ^ (e + 1)) :
    AbLaw.cst ((Y e).hom ≫ thick R I e) V a = 0 := by
  have h : (thick R I e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = 0 := by
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [← this]
    simp [Ideal.Quotient.eq_zero_iff_mem.2 ha]
  simp only [AbLaw.cst, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, h, map_zero]

theorem mul_eq_zero_of_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = 0 := by
  have h : x * y ∈ towerIdeal Y e (I ^ (e + 1)) V := by
    have h0 := Ideal.mul_mem_mul hx hy
    unfold towerIdeal at h0 ⊢
    rw [← Ideal.map_mul, ← pow_succ'] at h0
    exact h0
  have hb : towerIdeal Y e (I ^ (e + 1)) V = ⊥ := by
    unfold towerIdeal
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro a ha
    exact cst_eq_zero e V ha
  rw [hb] at h
  exact h

theorem mul_eq_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) : x * y = x' * y := by
  have := mul_eq_zero_of_mem e V hx hy
  rw [sub_mul] at this
  exact sub_eq_zero.1 this

theorem pow_mul_eq_pow_mul_of_sub_mem (e : ℕ) (V : (Y e).left.Opens) {x x' y : Γ((Y e).left, V)}
    (hx : x - x' ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) :
    x ^ m * y = x' ^ m * y :=
  mul_eq_mul_of_sub_mem e V (Ideal.mem_of_dvd _ (sub_dvd_pow_sub_pow x x' m) hx) hy

theorem pow_mul_eq_of_sub_one_mem (e : ℕ) (V : (Y e).left.Opens) {x y : Γ((Y e).left, V)}
    (hx : x - 1 ∈ towerIdeal Y e I V) (hy : y ∈ towerIdeal Y e (I ^ e) V) (m : ℕ) : x ^ m * y = y := by
  rw [pow_mul_eq_pow_mul_of_sub_mem e V hx hy m, one_pow, one_mul]

theorem rs_mem (e : ℕ) (J : Ideal R) {U V : (Y e).left.Opens} (h : V ≤ U) {x : Γ((Y e).left, U)}
    (hx : x ∈ towerIdeal Y e J U) : rs (Y e).left h x ∈ towerIdeal Y e J V := by
  unfold towerIdeal at hx ⊢
  have h1 := Ideal.mem_map_of_mem (rs (Y e).left h) hx
  rw [Ideal.map_map] at h1
  have h2 : (rs (Y e).left h).comp (AbLaw.cst ((Y e).hom ≫ thick R I e) U) = AbLaw.cst ((Y e).hom ≫ thick R I e) V :=
    RingHom.ext fun r => rs_cst _ h r
  rwa [h2] at h1

theorem isUnit_rs_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U))
    (hb : V ≤ X.basicOpen f) : IsUnit (rs X h f) := by
  have hu : IsUnit (rs X (X.basicOpen_le f) f) := X.toRingedSpace.isUnit_res_basicOpen f
  have := hu.map (rs X hb)
  rwa [rs_rs] at this

end GlobalTheory.FormalAlg.TowerH1

namespace GlobalTheory.FormalAlg.TowerH1

theorem ev_X {R : Type} [CommRing R] {I : Ideal R}
    {Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    {β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left} {n : ℕ} (C : Charts I Y β n) (e : ℕ) (i m : Fin (n + 1)) :
    C.ev e i (MvPolynomial.X m) = C.ρ e i m := by
  simp only [Charts.ev, MvPolynomial.eval₂Hom_X']

end GlobalTheory.FormalAlg.TowerH1


open GlobalTheory.FormalAlg.TowerH1 in
theorem GlobalTheory.FormalAlg.towerCech_h1_uniform : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (n : ℕ) (C : Charts I Y β n), ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → ∀ e : ℕ, (∀ c : ∀ i j, Γ((Y e).left, C.D e i ⊓ C.D e j), (∀ i j, c i j ∈ towerIdeal Y e (I ^ e) _) → (∀ i j l, rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j) (c i j) + rs (Y e).left (inf_le_left.trans inf_le_left : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (le_inf (inf_le_left.trans inf_le_right) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l) (c j l) = rs (Y e).left (le_inf (inf_le_left.trans inf_le_left) inf_le_right : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l) (c i l)) → ∃ a : ∀ i, Γ((Y e).left, C.D e i), (∀ i, a i ∈ towerIdeal Y e (I ^ e) _) ∧ ∀ i j, c i j = rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (a i) - rs (Y e).left (inf_le_left : C.D e i ⊓ C.D e j ≤ C.D e i) (C.ρ e i j) ^ k * rs (Y e).left (inf_le_right : C.D e i ⊓ C.D e j ≤ C.D e j) (a j)) := by
  intro R _ _ I Y β hβ n C
  classical
  let J : ℕ → Ideal (MvPolynomial (Fin (n + 1)) R) := fun e => ⨅ i, RingHom.ker (C.ev e i)
  have hJ : ∀ e F, F ∈ J e ↔ ∀ i, C.ev e i F = 0 := by
    intro e F
    simp only [J, Ideal.mem_iInf, RingHom.mem_ker]
  obtain ⟨d₀, hd₀⟩ := GlobalTheory.T.uniform_serre_vanishing_cech_cocycles R I n J (fun e t a F ha _ _ hF =>
    (hJ _ _).2 fun i => GlobalTheory.T.liftedRatios_eval_ideal_mul_eq_zero_succ R I Y β hβ n C e a F i ha ((hJ e F).1 hF i))
  refine ⟨d₀, fun k hk e c hc hcoc => ?_⟩
  have lev := GlobalTheory.T.thickeningTower_liftedRatios_projective_relations R I Y β hβ n C
  choose N₀ hN₀ using fun i j => GlobalTheory.T.exists_homogeneous_form_of_overlap_ideal_pow_thickening R I Y β hβ n C e i j (c i j) (hc i j)
  let N := Finset.univ.sup (fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2)
  have hN : ∀ i j, N₀ i j ≤ N := fun i j =>
    Finset.le_sup (f := fun p : Fin (n + 1) × Fin (n + 1) => N₀ p.1 p.2) (Finset.mem_univ (i, j))
  choose F hFh hFc hFe using fun i j => hN₀ i j N (hN i j) k
  have hFm : ∀ i j, F i j ∈ Ideal.map MvPolynomial.C (I ^ e) := fun i j =>
    MvPolynomial.mem_map_C_iff.2 (hFc i j)

  have htri : ∀ i j l, ∃ L : ℕ, ((MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) * MvPolynomial.X j * MvPolynomial.X l) ^ L *
      (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l) ∈ J e := by
    intro i j l
    have hH : (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l - MvPolynomial.X j ^ N * F i l :
        MvPolynomial (Fin (n + 1)) R).IsHomogeneous (N + (k + 2 * N)) :=
      (((MvPolynomial.isHomogeneous_X_pow l N).mul (hFh i j)).add
        ((MvPolynomial.isHomogeneous_X_pow i N).mul (hFh j l))).sub
        ((MvPolynomial.isHomogeneous_X_pow j N).mul (hFh i l))
    have hHc : ∀ m, AddMonoidAlgebra.coeff (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l : MvPolynomial (Fin (n + 1)) R) m ∈ I ^ e :=
      MvPolynomial.mem_map_C_iff.1 (sub_mem (add_mem (Ideal.mul_mem_left _ _ (hFm i j))
        (Ideal.mul_mem_left _ _ (hFm j l))) (Ideal.mul_mem_left _ _ (hFm i l)))

    have hTij : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e j := inf_le_left
    have hTil : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have hTjl : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j ⊓ C.D e l := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hTi : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e i := inf_le_left.trans inf_le_left
    have hTj : C.D e i ⊓ C.D e j ⊓ C.D e l ≤ C.D e j := inf_le_left.trans inf_le_right
    have h1 : rs (Y e).left hTi (C.ev e i (F i j)) =
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTij (c i j) := by
      have := congrArg (rs (Y e).left hTij) (hFe i j)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h3 : rs (Y e).left hTi (C.ev e i (F i l)) =
        rs (Y e).left hTi (C.ρ e i l) ^ N * rs (Y e).left hTil (c i l) := by
      have := congrArg (rs (Y e).left hTil) (hFe i l)
      simpa only [rs_rs, map_mul, map_pow] using this
    have h2 : rs (Y e).left hTi (C.ev e i (F j l)) =
        rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * (rs (Y e).left hTj (C.ρ e j l) ^ N *
          rs (Y e).left hTjl (c j l)) := by
      have t1 := congrArg (rs (Y e).left hTij)
        (GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + 2 * N) (F j l) (hFh j l) (hFc j l) i j).2.2
      have t2 := congrArg (rs (Y e).left hTjl) (hFe j l)
      simp only [rs_rs, map_mul, map_pow] at t1 t2
      rw [t1, t2]
    have hcjl : rs (Y e).left hTjl (c j l) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hTjl (hc j l)
    have hP : rs (Y e).left hTi (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTi (lev.2.1 e i)
      rwa [map_sub, map_one] at this
    have hB : rs (Y e).left hTi (C.ρ e i l) - rs (Y e).left hTi (C.ρ e i j) * rs (Y e).left hTj (C.ρ e j l)
        ∈ towerIdeal Y e I _ := by
      have := rs_mem e I hTij (lev.2.2 e i j l)
      simpa only [map_sub, map_mul, rs_rs] using this
    have e1 := pow_mul_eq_of_sub_one_mem e _ hP hcjl N
    have e2 := pow_mul_eq_pow_mul_of_sub_mem e _ hB hcjl N
    have hyp := hcoc i j l
    have hz : rs (Y e).left hTi (C.ev e i (MvPolynomial.X l ^ N * F i j + MvPolynomial.X i ^ N * F j l -
        MvPolynomial.X j ^ N * F i l)) = 0 := by
      simp only [map_add (f := _), map_sub, map_mul, map_pow, ev_X]
      rw [h1, h2, h3]
      linear_combination (rs (Y e).left hTi (C.ρ e i j) ^ (k + 2 * N) * rs (Y e).left hTj (C.ρ e j l) ^ N) * e1 -
        rs (Y e).left hTi (C.ρ e i j) ^ (k + N) * e2 +
        rs (Y e).left hTi (C.ρ e i j) ^ N * rs (Y e).left hTi (C.ρ e i l) ^ N * hyp
    obtain ⟨L, hL⟩ := GlobalTheory.T.homogeneousForm_killed_by_power_of_tripleChart_product R I Y β hβ n C e _ _ hH hHc i j l hz
    exact ⟨L, (hJ _ _).2 hL⟩

  obtain ⟨N', G, hGh, hGc, hrel⟩ := hd₀ k hk e N F hFh hFc htri
  have tr := fun i j => GlobalTheory.T.homogeneousForm_chart_change_coeff_ideal_pow R I Y β hβ n C e (k + N') (G j) (hGh j) (hGc j) i j
  refine ⟨fun i => C.ev e i (G i), fun i => (tr i i).1, fun i j => ?_⟩
  obtain ⟨L, hL⟩ := hrel i j
  have hl : C.D e i ⊓ C.D e j ≤ C.D e i := inf_le_left
  have hr : C.D e i ⊓ C.D e j ≤ C.D e j := inf_le_right
  have h0 := congrArg (rs (Y e).left hl) ((hJ _ _).1 hL i)
  simp only [map_mul, map_sub, map_pow, ev_X, map_zero] at h0
  rw [hFe i j, (tr i j).2.2] at h0
  have hci := hc i j
  have hai : rs (Y e).left hl (C.ev e i (G i)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hl (tr i i).1
  have haj : rs (Y e).left hr (C.ev e j (G j)) ∈ towerIdeal Y e (I ^ e) _ := rs_mem e _ hr (tr j j).1
  have hP : rs (Y e).left hl (C.ρ e i i) - 1 ∈ towerIdeal Y e I _ := by
    have := rs_mem e I hl (lev.2.1 e i)
    rwa [map_sub, map_one] at this
  have ec := pow_mul_eq_of_sub_one_mem e _ hP hci (L + N')
  have ea := pow_mul_eq_of_sub_one_mem e _ hP hai (L + N)
  have eb := pow_mul_eq_of_sub_one_mem e _ hP haj (L + N + N')
  have hu : IsUnit (rs (Y e).left hl (C.ρ e i j) ^ (L + N + N')) :=
    (isUnit_rs_of_le_basicOpen hl _ (lev.1 e i j).ge).pow _
  have hw : rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * (c i j - (rs (Y e).left hl (C.ev e i (G i)) -
      rs (Y e).left hl (C.ρ e i j) ^ k * rs (Y e).left hr (C.ev e j (G j)))) = 0 := by
    linear_combination h0 - rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ec +
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N') * ea -
      rs (Y e).left hl (C.ρ e i j) ^ (L + N + N' + k) * eb
  exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hw)
