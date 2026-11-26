module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRYBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

set_option autoImplicit false

private lemma int_range {L A : Type} [Field L] [Algebra ℂ L] [CommRing A] [Algebra ℂ A] [Algebra A L]
    [IsScalarTower ℂ A L] (hA : ∀ a : A, a ∈ (algebraMap ℂ A).range) {y : L} (h : IsIntegral A y) :
    y ∈ (algebraMap ℂ L).range := by
  haveI : Algebra.IsIntegral ℂ A := ⟨fun a => by
    obtain ⟨c, rfl⟩ := hA a
    exact isIntegral_algebraMap⟩
  have hy : IsIntegral ℂ y := isIntegral_trans y h
  exact minpoly.mem_range_of_degree_eq_one ℂ y
    (IsAlgClosed.degree_eq_one_of_irreducible ℂ (minpoly.irreducible hy))

private lemma int_mono {E L : Type} [CommRing E] [Algebra ℂ E] [CommRing L] [Algebra E L]
    {A B : Subalgebra ℂ E} (h : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hp, he⟩ := hy
  refine ⟨p.map (Subalgebra.inclusion h).toRingHom, hp.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact he

private lemma int_scale {L : Type} [Field L] [Algebra ℂ L] (A A' : Subalgebra ℂ L) (s : L) (hs : s ∈ A)
    (hc : ∀ c ∈ A', ∃ N : ℕ, s ^ N * c ∈ A) {y : L} (hy : IsIntegral A' y) :
    ∃ N : ℕ, IsIntegral A (y * s ^ N) := by
  obtain ⟨p, hp, he⟩ := hy
  set q : Polynomial L := p.map (algebraMap A' L) with hq
  have hqm : q.Monic := hp.map _
  have hqe : q.eval₂ (RingHom.id L) y = 0 := by
    rw [hq, Polynomial.eval₂_map]
    simpa using he
  have hcoef : ∀ i, q.coeff i ∈ A' := fun i => by
    rw [hq, Polynomial.coeff_map]
    exact (p.coeff i).2
  have hM : ∀ t : Finset ℕ, ∃ M : ℕ, ∀ i ∈ t, s ^ M * q.coeff i ∈ A := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | insert a t _ ih =>
      obtain ⟨M, hM⟩ := ih
      obtain ⟨N, hN⟩ := hc _ (hcoef a)
      refine ⟨M + N, fun i hi => ?_⟩
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) hN
      · rw [add_comm, pow_add, mul_assoc]
        exact A.mul_mem (A.pow_mem hs _) (hM i hi)
  obtain ⟨M, hM⟩ := hM (Finset.range (q.natDegree + 1))
  refine ⟨M, ?_⟩
  have hrm : (Polynomial.scaleRoots q (s ^ M)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hqm
  have hre : (Polynomial.scaleRoots q (s ^ M)).eval₂ (RingHom.id L) (y * s ^ M) = 0 := by
    have := Polynomial.scaleRoots_eval₂_mul (p := q) (RingHom.id L) y (s ^ M)
    rw [hqe, mul_zero] at this
    rw [mul_comm]
    exact this
  have hA : ∀ i, (Polynomial.scaleRoots q (s ^ M)).coeff i ∈ A := by
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i q.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, q.natDegree - i = k + 1 := ⟨q.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, mul_comm, mul_assoc]
      refine A.mul_mem (A.pow_mem (A.pow_mem hs _) _) ?_
      rw [mul_comm]
      exact mul_comm (s ^ M) (q.coeff i) ▸ hM i (Finset.mem_range.2 (by omega))
    · subst hi
      simp [hqm.coeff_natDegree, A.one_mem]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact A.zero_mem
  have hlift : Polynomial.scaleRoots q (s ^ M) ∈ Polynomial.lifts (algebraMap A L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    exact ⟨⟨_, hA i⟩, rfl⟩
  obtain ⟨r, hr, -, hrm'⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hrm
  refine ⟨r, hrm', ?_⟩
  rw [← hr, Polynomial.eval₂_map] at hre
  simpa using hre

private lemma omB_mono' {L : Type} [Field L] [Algebra ℂ L] {B B' : Subalgebra ℂ L} (h : B ≤ B') (q : ℕ) :
    omB ℂ L B q ≤ omB ℂ L B' q :=
  Submodule.span_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, h hb, v, fun j => h (hv j), e⟩

private lemma omB_stab {L : Type} [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (q : ℕ) :
    Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) := by
  intro r hr m hm
  induction hm using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨b, hb, v, hv, rfl⟩ := hz
    exact Submodule.subset_span ⟨r * b, B.mul_mem hr hb, v, hv, by simp [mul_smul]⟩
  | zero => simp
  | add a c _ _ ha hc =>
    rw [map_add (f := _)]
    exact add_mem ha hc
  | smul t a _ ha =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ ha

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] {d : ℕ} (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K')

private lemma rA_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rA ℂ x I ≤ rA ℂ x I' :=
  Algebra.adjoin_mono fun _ ⟨i, hi, j, e⟩ => ⟨i, h hi, j, e⟩

private lemma rB_mono' {I I' : Finset (Fin (d + 1))} (h : I ⊆ I') : rB ℂ K x I ≤ rB ℂ K x I' :=
  fun _ hy => int_mono (rA_mono' x h) hy

private lemma integralClosure_mono_subset {J J' : Finset (Fin (d + 1))} (h : J ⊆ J') : R2 x j2 J ≤ R2 x j2 J' :=
  fun _ hy => int_mono (Subalgebra.map_mono (rB_mono' x h)) hy

private lemma ratio_mem {I : Finset (Fin (d + 1))} {i : Fin (d + 1)} (hi : i ∈ I) (a : Fin (d + 1)) :
    x a / x i ∈ rA ℂ x I :=
  Algebra.subset_adjoin ⟨i, hi, a, rfl⟩

private lemma rA_mem_rB {I : Finset (Fin (d + 1))} {f : F} (hf : f ∈ rA ℂ x I) :
    algebraMap F K f ∈ rB ℂ K x I :=
  show IsIntegral (rA ℂ x I) (algebraMap F K f) from
    isIntegral_algebraMap (R := rA ℂ x I) (A := K) (x := ⟨f, hf⟩)

private lemma rB_empty {b : K} (hb : b ∈ rB ℂ K x ∅) : b ∈ (algebraMap ℂ K).range := by
  refine int_range (A := rA ℂ x ∅) (fun a => ?_) hb
  have h0 : rA ℂ x ∅ = ⊥ := by simp [rA]
  have ha : (a : F) ∈ (⊥ : Subalgebra ℂ F) := h0 ▸ a.2
  obtain ⟨c, hc⟩ := Algebra.mem_bot.1 ha
  exact ⟨c, Subtype.ext hc⟩

private lemma integralClosure_empty_const {y : K'} (hy : y ∈ R2 x j2 ∅) : y ∈ (algebraMap ℂ K').range := by
  refine int_range (A := (rB ℂ K x ∅).map j2) (fun a => ?_) hy
  obtain ⟨b, hb, hba⟩ := a.2
  obtain ⟨c, rfl⟩ := rB_empty x hb
  exact ⟨c, Subtype.ext (by rw [← hba]; simp)⟩

private lemma j2_mem_R2_of_mem_rB {J : Finset (Fin (d + 1))} {b : K} (hb : b ∈ rB ℂ K x J) : j2 b ∈ R2 x j2 J :=
  show IsIntegral ((rB ℂ K x J).map j2) (j2 b) from
    isIntegral_algebraMap (R := (rB ℂ K x J).map j2) (A := K') (x := ⟨j2 b, b, hb, rfl⟩)

private lemma rB_shift (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {b : K}
    (hb : b ∈ rB ℂ K x (insert j' J)) : ∃ N : ℕ, algebraMap F K (x j' / x j) ^ N * b ∈ rB ℂ K x J := by
  by_cases hj' : j' ∈ J
  · refine ⟨0, ?_⟩
    rw [Finset.insert_eq_of_mem hj'] at hb
    simpa using hb
  · obtain ⟨N, hN⟩ := ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h (insert j' J) j (Finset.mem_insert_of_mem hj)).2 b).1 hb
    refine ⟨N, ((GlobalTheory.T.finite_cover_ring_localization_chart ℂ F K d x h J j hj).2 _).2 ⟨N, ?_⟩⟩
    rw [Finset.prod_insert hj', map_mul, mul_pow] at hN
    convert hN using 1
    ring

private lemma integralClosure_shift_power (h : IsFinCover ℂ K x) {J : Finset (Fin (d + 1))} {j j' : Fin (d + 1)} (hj : j ∈ J) {y : K'}
    (hy : y ∈ R2 x j2 (insert j' J)) : ∃ N : ℕ, y * j2 (algebraMap F K (x j' / x j)) ^ N ∈ R2 x j2 J := by
  have hs : j2 (algebraMap F K (x j' / x j)) ∈ (rB ℂ K x J).map j2 :=
    ⟨_, rA_mem_rB x (ratio_mem x hj j'), rfl⟩
  obtain ⟨N, hN⟩ := int_scale ((rB ℂ K x J).map j2) ((rB ℂ K x (insert j' J)).map j2) _ hs (by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨N, hN⟩ := rB_shift x h hj hb
    exact ⟨N, ⟨_, hN, by simp⟩⟩) hy
  exact ⟨N, hN⟩

end

theorem UpperTheory.Gal.productCup_of_system.rYBasic_of :
    RYBasic := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY
  have hpull : ∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I := by
    intro I b hb
    have hb' : IsIntegral (rA ℂ (xv x) I) b := hb
    exact (IsIntegral.algebraMap hb' : IsIntegral (rA ℂ (xv x) I) (algebraMap K K' b))
  have hmono : ∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J' :=
    fun I I' J J' hI hJ => sup_le_sup (rB_mono' (xv x) hI) (integralClosure_mono_subset (xv x) j2 hJ)
  refine ⟨fun I => ?_, fun a => ?_, hmono, fun I b hb => ⟨hpull I b hb, j2_mem_R2_of_mem_rB (xv x) j2 hb⟩, ?_⟩
  · refine sup_eq_left.2 fun y hy => ?_
    obtain ⟨c, rfl⟩ := integralClosure_empty_const (xv x) j2 hy
    exact (rB ℂ K' (xv x) I).algebraMap_mem c
  · refine ⟨fun I I' J J' _ _ hI hJ => hmono I I' J J' hI hJ,
      fun I I' J J' _ _ hI hJ => omB_mono' (hmono I I' J J' hI hJ) a,
      fun I J _ _ => omB_stab _ a, fun I J _ i hi b => ?_, fun I J _ j hj b => ?_⟩
    · have e : (((sysY x j2 a).X b * ((sysY x j2 a).X i)⁻¹ : K'ˣ) : K') = algebraMap F K' (xv x b / xv x i) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_left : rB ℂ K' (xv x) I ≤ RY (xv x) j2 I J) (rA_mem_rB (xv x) (ratio_mem (xv x) hi b))
    · have e : (((sysY x j2 a).Y b * ((sysY x j2 a).Y j)⁻¹ : K'ˣ) : K') = j2 (algebraMap F K (xv x b / xv x j)) := by
        simp [sysY, map_div₀, div_eq_mul_inv]
      rw [e]
      exact (le_sup_right : R2 (xv x) j2 J ≤ RY (xv x) j2 I J)
        (j2_mem_R2_of_mem_rB (xv x) j2 (rA_mem_rB (xv x) (ratio_mem (xv x) hj b)))
  · intro J j hj j' y hy
    exact integralClosure_shift_power (xv x) j2 hY.covZ hj hy
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PIdVal
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

section Vals
variable {L : Type} [Field L] [Algebra ℂ L] {B : Subalgebra ℂ L} {e : B →ₐ[ℂ] ℂ}

private lemma val_mul (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v * v') (c * c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨mul_mem p p', map_mul ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_add (hV : ValBasic) {v v' : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v' c') :
    Val B e (v + v') (c + c') := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  exact (hev _ _).2 ⟨add_mem p p', map_add ev ⟨v, p⟩ ⟨v', p'⟩⟩

private lemma val_zero (hV : ValBasic) : Val B e (0 : L) 0 := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact (hev _ _).2 ⟨zero_mem _, map_zero ev⟩

private lemma val_sum (hV : ValBasic) {ι : Type} (s : Finset ι) (f : ι → L) (c : ι → ℂ)
    (h : ∀ i ∈ s, Val B e (f i) (c i)) : Val B e (∑ i ∈ s, f i) (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_zero hV
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact val_add hV (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private lemma val_unique (hV : ValBasic) {v : L} {c c' : ℂ} (h : Val B e v c) (h' : Val B e v c') :
    c = c' := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  obtain ⟨p, rfl⟩ := (hev _ _).1 h
  obtain ⟨p', rfl⟩ := (hev _ _).1 h'
  rfl

private lemma val_of_mem (hV : ValBasic) {v : L} (h : v ∈ loc B e) : ∃ c, Val B e v c := by
  obtain ⟨-, ⟨ev, hev⟩, -, -⟩ := hV L B e
  exact ⟨_, (hev _ _).2 ⟨h, rfl⟩⟩

end Vals

section
variable {F K : Type} [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K]

private lemma muP_tmul (τ : DR ℂ K →ₗ[K] K) (w' w'' w : DR ℂ K) :
    muP F K τ (w' ⊗ₜ w'') w = (Algebra.trace F K (τ (w' * w))) ⊗ₜ[ℂ] w'' := by
  simp [muP]

private lemma mulP_tmul (f : F) (w : DR ℂ K) : mulP F K (f ⊗ₜ w) = algebraMap F K f • w := by
  simp [mulP]

private lemma acts_expand (τ : DR ℂ K →ₗ[K] K) {m : ℕ} (w' w : Fin m → DR ℂ K) (v : DR ℂ K) :
    mulP F K (muP F K τ (∑ k, w' k ⊗ₜ w k) v) =
      ∑ k, algebraMap F K (Algebra.trace F K (τ (w' k * v))) • w k := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, muP_tmul, mulP_tmul]

private lemma omG_ne {d : ℕ} (x : Fin (d + 1) → Fˣ) : algebraMap F K (omG x 0) ≠ 0 := by
  refine (map_ne_zero _).2 ?_
  exact Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero

end

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.idVal_of :
    LocForms → DtBasic → CRT → TrVal → ResVal → LatA → ValBasic → OmLoc → IdVal := by
  intro hLF hDt hCRT hTV hRV hLat hV hOL F K _ _ _ _ _ _ d x cov τ hτ red a ha m w' w hw hact z
  classical
  obtain ⟨hli, hdt, hvol, -, -⟩ := hDt F K d x cov τ hτ
  set B := rB ℂ K (xv x) ({0} : Finset (Fin (d + 1))) with hB
  set om : K := algebraMap F K (omG x 0) with hom
  have omne : om ≠ 0 := omG_ne x
  have hτv : τ (dtS K x Finset.univ) = om := by
    rw [hvol, map_smul, hτ.1, smul_eq_mul, mul_one]
  have hgEq : ∀ y ∈ omB ℂ K B d, y = (τ y / om) • dtS K x Finset.univ := by
    intro y hy
    have h1 := (GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K d (xv x) cov).2 τ hτ y (mem_deg_of_mem_omB B d y hy)
    rw [hvol, smul_smul, div_mul_cancel₀ _ omne]
    exact h1
  have hgLoc : ∀ (e : fib ℂ K (xv x)), ∀ y ∈ omB ℂ K B d, τ y / om ∈ loc B e.1 := by
    intro e y hy
    have hle : B ≤ loc B e.1 := (hV K B e.1).1
    have hy' := (hOL K B e.1 d).2.2 _ hle hy
    obtain ⟨c, hc, hce⟩ := (hLF F K d x cov red e d y).1 hy'
    have hp : Finset.univ.powersetCard d = ({Finset.univ} : Finset (Finset (Fin d))) := by
      have := Finset.powersetCard_self (Finset.univ : Finset (Fin d))
      simpa using this
    rw [hp, Finset.sum_singleton] at hce
    have : τ y = c Finset.univ * om := by
      rw [hce, map_smul, hτv, smul_eq_mul]
    rw [this, mul_div_cancel_right₀ _ omne]
    exact hc _
  have hyB : ∀ k (S : Finset (Fin d)), S.card = a → w' k * dtS K x S ∈ omB ℂ K B d := by
    intro k S hS
    have := mul_mem_omB B (d - a) a _ (hw k).1 _ (hS ▸ hdt S)
    rwa [Nat.sub_add_cancel ha] at this
  have hwL : ∀ k, ∃ c : Finset (Fin d) → K, (∀ S, c S ∈ loc B z.1) ∧
      w k = ∑ S ∈ Finset.univ.powersetCard a, c S • dtS K x S := fun k =>
    (hLF F K d x cov red z a (w k)).1 ((hOL K B z.1 a).2.2 _ (hV K B z.1).1 (hw k).2)
  choose b hbl hbe using hwL
  have hφ : ∀ v : K, ∃ c : ℂ, v ∈ loc B z.1 → Val B z.1 v c := by
    intro v
    by_cases hv : v ∈ loc B z.1
    · obtain ⟨c, hc⟩ := val_of_mem hV hv
      exact ⟨c, fun _ => hc⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose φ hφ using hφ
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_laurentConstantTermForm_functionField ℂ F d (xv x) cov.pd
  refine ⟨fun k S => τ (w' k * dtS K x S) / om, b, fun k S => φ (τ (w' k * dtS K x S) / om),
    fun k T => φ (b k T), fun k S hS => hgEq _ (hyB k S hS), hbe, fun k S hS =>
      ⟨hφ _ (hgLoc z _ (hyB k S hS)), hφ _ (hbl k S)⟩, ?_⟩
  intro S T hS hT
  obtain ⟨h, hh⟩ := (hCRT F K d x cov).2 (fun e => if e = z then 1 else 0)
  set g : Fin m → K := fun k => τ (w' k * dtS K x S) / om with hg
  set t : Fin m → F := fun k => Algebra.trace F K (g k * h) with ht
  have hgy : ∀ k, τ (w' k * dtS K x S) = om * g k := by
    intro k
    simp only [hg]
    field_simp
  have htr : ∀ k, Algebra.trace F K (om * (g k * h)) = omG x 0 * t k := by
    intro k
    rw [hom, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have claim1 : ∀ k, t k ∈ rA ℂ (xv x) {0} := by
    intro k
    have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K d (xv x) cov τ hτ {0} ⟨0, by simp⟩ (om * (g k * h))).2
      ⟨(h : K) • (w' k * dtS K x S), smul_mem_omB B d _ h.2 _ (hyB k S hS), by
        rw [map_smul, hgy, smul_eq_mul]; ring⟩ 1 (Subalgebra.one_mem _)
    rw [mul_one, htr] at h1
    have h2 := ((hLat F d x cov.pd {0} 0 (by simp)).2.1 _).1 h1
    have hne : omG x 0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => div_ne_zero (x l).ne_zero (x 0).ne_zero
    rwa [mul_div_cancel_left₀ _ hne] at h2
  have claim2 : ∀ k, Val B z.1 (algebraMap F K (t k)) (φ (g k)) := by
    intro k
    have hres := hRV F K d x cov ρ hρ z (t k) (claim1 k)
    have hγ0 : ∀ e : fib ℂ K (xv x), ∃ c, Val B e.1 (g k) c := fun e =>
      val_of_mem hV (hgLoc e _ (hyB k S hS))
    choose γ0 hγ0 using hγ0
    have hγ : ∀ e : fib ℂ K (xv x), Val B e.1 (g k * h) (γ0 e * e.1 h) := fun e =>
      val_mul hV (hγ0 e) ((hV K B e.1).2.2.1 h)
    have htv := hTV F K d x cov red ρ hρ (g k * h) (fun e => γ0 e * e.1 h) hγ (claim1 k)
    have hfs : ∑ᶠ e, γ0 e * e.1 h = φ (g k) := by
      rw [finsum_eq_single _ z]
      · rw [hh z]
        simp only [if_true, mul_one]
        exact val_unique hV (hγ0 z) (hφ _ (hgLoc z _ (hyB k S hS)))
      · intro e he
        rw [hh e, if_neg he, mul_zero]
    have : ρ (t k) = φ (g k) := by rw [← hfs]; exact htv
    rwa [this] at hres
  have claim3 : ∑ k, algebraMap F K (t k) • w k = (h : K) • dtS K x S := by
    have h1 := hact ((h : K) • dtS K x S)
      (Submodule.smul_mem _ _ (hS ▸ mem_deg_of_mem_omB B _ _ (hdt S)))
    rw [acts_expand] at h1
    have h2 : ∀ k, algebraMap F K (Algebra.trace F K (τ (w' k * ((h : K) • dtS K x S)))) • w k =
        om • (algebraMap F K (t k) • w k) := by
      intro k
      rw [mul_smul_comm, map_smul, hgy, smul_eq_mul,
        show (h : K) * (om * g k) = om * (g k * h) by ring, htr, map_mul, mul_smul]
    simp only [h2, ← Finset.smul_sum] at h1
    exact smul_right_injective _ omne h1
  have claim4 : ∀ T ∈ Finset.univ.powersetCard a,
      ∑ k, algebraMap F K (t k) * b k T = if S = T then (h : K) else 0 := by
    have hsum : ∑ T ∈ Finset.univ.powersetCard a,
        ((∑ k, algebraMap F K (t k) * b k T) - if S = T then (h : K) else 0) • dtS K x T = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, ← hbe]
      rw [claim3, Finset.sum_ite_eq, if_pos (by simp [Finset.mem_powersetCard, hS]), sub_self]
    intro T hT
    exact sub_eq_zero.1 (linearIndependent_iff'.1 hli _ _ hsum T hT)
  have hTm : T ∈ Finset.univ.powersetCard a := by simp [Finset.mem_powersetCard, hT]
  have hL : Val B z.1 (∑ k, algebraMap F K (t k) * b k T) (∑ k, φ (g k) * φ (b k T)) :=
    val_sum hV _ _ _ fun k _ => val_mul hV (claim2 k) (hφ _ (hbl k T))
  rw [claim4 T hTm] at hL
  have hz1 : Val B z.1 (h : K) 1 := by
    have := (hV K B z.1).2.2.1 h
    rwa [hh z, if_pos rfl] at this
  by_cases hST : S = T
  · rw [if_pos hST] at hL ⊢
    exact val_unique hV hL hz1
  · rw [if_neg hST] at hL ⊢
    exact val_unique hV hL (val_zero hV)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrTop
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUnique
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem smul_smul_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] (c : K) (x : L) (ω : DR k K) :
    (c • x) • mapDR k K L ω = x • mapDR k K L (c • ω) := by
  rw [map_smul, smul_assoc, smul_comm]

theorem trDR_isTrDR_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L],
    IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  intro k K L _ _ _ _ _ _ _ _ _
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L
  have uniq : ∀ T T' : DR k L →ₗ[k] DR k K, IsTrDR k K L T → IsTrDR k K L T' → T = T' := by
    intro T T' hT hT'
    refine LinearMap.ext fun y => ?_
    obtain ⟨m, b, ω, rfl⟩ := hspan y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hT, hT']
  let e := Module.finBasis K L
  let n := Module.finrank K L
  let φ : (Fin n → DR k K) →ₗ[k] DR k L :=
    { toFun := fun ω => ∑ j, e j • mapDR k K L (ω j)
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← algebraMap_smul K c (a j), map_smul, algebraMap_smul, smul_comm] }
  have hφ : Function.Bijective φ := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro ω hω
      funext j
      exact hind n e ω e.linearIndependent hω j
    · intro y
      obtain ⟨m, b, ω, rfl⟩ := hspan y
      refine ⟨fun j => ∑ i, e.repr (b i) j • ω i, ?_⟩
      change ∑ j, e j • mapDR k K L (∑ i, e.repr (b i) j • ω i) = _
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.smul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
  let ψ := (LinearEquiv.ofBijective φ hφ).symm
  let g : (Fin n → DR k K) →ₗ[k] DR k K :=
    { toFun := fun ω => ∑ j, Algebra.trace K L (e j) • ω j
      map_add' := fun a b => by simp [smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_comm] }
  have ex : IsTrDR k K L (g ∘ₗ ψ.toLinearMap) := by
    intro b ω
    have hb : b • mapDR k K L ω = φ (fun j => e.repr b j • ω) := by
      change _ = ∑ j, e j • mapDR k K L (e.repr b j • ω)
      simp only [← smul_smul_mapDR]
      rw [← Finset.sum_smul, e.sum_repr]
    rw [LinearMap.comp_apply, hb]
    have : ψ (φ (fun j => e.repr b j • ω)) = fun j => e.repr b j • ω :=
      (LinearEquiv.ofBijective φ hφ).symm_apply_apply _
    rw [LinearEquiv.coe_coe, this]
    change ∑ j, Algebra.trace K L (e j) • e.repr b j • ω = _
    simp only [smul_smul, ← Finset.sum_smul]
    congr 1
    conv_rhs => rw [← e.sum_repr b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, mul_comm]
  have htr : IsTrDR k K L (trDR k K L) := by
    have h : ∃ T, IsTrDR k K L T := ⟨_, ex⟩
    unfold trDR
    rw [dite_eq_left h]
    exact h.choose_spec
  exact ⟨htr, fun T hT => uniq T _ hT htr⟩

end GlobalTheory.W1
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceExistsUniqueStatement
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_exists_unique : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], IsTrDR k K L (trDR k K L) ∧ ∀ T, IsTrDR k K L T → T = trDR k K L := by
  first | (exact @GlobalTheory.W1.trDR_isTrDR_unique) | (exact GlobalTheory.W1.trDR_isTrDR_unique) | (intros; apply GlobalTheory.W1.trDR_isTrDR_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormula
set_option autoImplicit false

noncomputable section

open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.W1

theorem trDR_projection : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L),
    trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  intro k K L _ _ _ _ _ _ _ _ _ α β
  obtain ⟨m, b, ω, rfl⟩ := (GlobalTheory.T.mapDR_span_and_linearIndependent_baseChange k K L).1 β
  have hT := (GlobalTheory.T.deRhamFormTrace_exists_unique k K L).1
  constructor
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.mul_sum, map_sum, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, ← map_mul, hT, hT, mul_smul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [Finset.sum_mul, map_sum, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_mul_assoc, ← map_mul, hT, hT, smul_mul_assoc]

end GlobalTheory.W1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamFormTraceProjectionFormulaStatement
open GlobalTheory.W1 GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRhamFormTrace_projection_formula : ∀ (k K L : Type) [Field k] [CharZero k] [Field K] [Field L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [FiniteDimensional K L], ∀ (α : DR k K) (β : DR k L), trDR k K L (mapDR k K L α * β) = α * trDR k K L β ∧ trDR k K L (β * mapDR k K L α) = trDR k K L β * α := by
  first | (exact @GlobalTheory.W1.trDR_projection) | (exact GlobalTheory.W1.trDR_projection) | (intros; apply GlobalTheory.W1.trDR_projection <;> assumption)
end
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem kahlerMap_volumeForm {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K']
    [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K']
    [IsScalarTower ℂ F K'] {d : ℕ} (x : Fin (d + 1) → F) :
    mapDR ℂ K K' (vol0 ℂ K x) = vol0 ℂ K' x := by
  simp only [vol0, ExteriorAlgebra.ιMulti_apply]
  rw [map_list_prod]
  congr 1
  simp only [List.map_ofFn]
  congr 1
  funext j
  have h1 : ∀ w : Ω[K⁄ℂ], mapDR ℂ K K' (ExteriorAlgebra.ι K w) = map1 ℂ K K' w := fun w => by
    simp [mapDR]
  have h2 : ∀ a : K, map1 ℂ K K' (D ℂ K a) = ExteriorAlgebra.ι K' (D ℂ K' (algebraMap K K' a)) := fun a => by
    simp [map1, ι1, KaehlerDifferential.map_D]
  simp only [Function.comp, h1, map_smul, h2, map_inv₀]
  rw [← algebraMap_smul K' ((algebraMap F K (x j.succ / x 0))⁻¹), map_inv₀, ← IsScalarTower.algebraMap_apply]

theorem UpperTheory.Gal.productCup_of_system.trTop_of :
    TrTop := by
  intro F K K' _ _ _ _ _ _ _ _ _ _ _ _ _ d x j2 hY τ hτ ρ hρ
  haveI : FiniteDimensional F K := hY.covZ.fin
  haveI : FiniteDimensional F K' := hY.covY.fin
  haveI : FiniteDimensional K K' := FiniteDimensional.right F K K'
  have hTr := (GlobalTheory.T.deRhamFormTrace_exists_unique ℂ K K').1
  have second : ∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h) := by
    intro h
    rw [← kahlerMap_volumeForm (K := K) (K' := K') (xv x), hTr h (vol0 ℂ K (xv x))]
    simp only [trF, LinearMap.comp_apply, LinearMap.restrictScalars_apply, map_smul, hτ.1, smul_eq_mul, mul_one]
    rw [Algebra.trace_trace]
  refine ⟨fun w y => ((GlobalTheory.T.deRhamFormTrace_projection_formula ℂ K K') w y).1, second, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨⟨τ', hτ'⟩, hvol⟩ := GlobalTheory.T.exists_topDegreeCoefficientForm_and_eq_on_top_forms ℂ F K' d (xv x) hY.covY
  have key : ∀ i : Fin (d + 1), trF ℂ τ ρ (trDR ℂ K K' (y' (Finset.univ.erase i))) = 0 := by
    intro i
    have hm : y' (Finset.univ.erase i) ∈ (if (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty ∧
        (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 then
        omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d else ⊥ : Submodule ℂ (DR ℂ K')) :=
      hy' (Finset.univ.erase i) (Set.mem_univ _)
    by_cases hne : (Finset.univ.erase i : Finset (Fin (d + 1))).Nonempty
    · have hc : (((Finset.univ.erase i : Finset (Fin (d + 1))).card : ℕ) : ℤ) = ((d : ℤ) - 1) + 1 := by
        simp
      rw [if_pos ⟨hne, hc⟩] at hm
      have hle : omB ℂ K' (rB ℂ K' (xv x) (Finset.univ.erase i)) d ≤ (⋀[K']^d Ω[K'⁄ℂ]).restrictScalars ℂ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨b, -, v, -, rfl⟩
        refine (⋀[K']^d Ω[K'⁄ℂ]).smul_mem b ?_
        rw [← ExteriorAlgebra.ιMulti_span_fixedDegree]
        exact Submodule.subset_span ⟨_, rfl⟩
      rw [hvol τ' hτ' _ (hle hm), second]
      have h1 := (GlobalTheory.T.complementaryModule_standardOpens_iff ℂ F K' d (xv x) hY.covY τ' hτ' _ hne (τ' (y' (Finset.univ.erase i)))).2 ⟨_, hm, rfl⟩ 1
        (one_mem _)
      rw [mul_one] at h1
      exact GlobalTheory.T.residue_functional_vanishes_on_omega_forms ℂ F d (xv x) hY.covY.pd ρ hρ i _ hne (by simp) _ h1
    · rw [if_neg (fun h => hne h.1)] at hm
      rw [(Submodule.mem_bot ℂ).1 hm]
      simp
  change trF ℂ τ ρ (trDR ℂ K K' (∑ i ∈ Finset.univ, _ • y' (Finset.univ.erase i))) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [map_zsmul, map_zsmul, key i, smul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PTrVal
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.productCup_of_system.PartialTraceValue

private theorem nakGen {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map (algebraMap A B) = ⊤) : ∃ r : A, r - 1 ∈ I ∧ algebraMap A B r ∈ 𝔟 := by
  let N : Submodule A B := 𝔟.restrictScalars A
  have key : ∀ j ∈ I.map (algebraMap A B), ∀ b : B,
      (Submodule.Quotient.mk (j * b) : B ⧸ N) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
    intro j hj
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hj
    · rintro _ ⟨i, hi, rfl⟩ b
      rw [← Algebra.smul_def, Submodule.Quotient.mk_smul]
      exact Submodule.smul_mem_smul hi Submodule.mem_top
    · intro b
      rw [zero_mul]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv b
      rw [add_mul, Submodule.Quotient.mk_add]
      exact Submodule.add_mem _ (hu b) (hv b)
    · intro c u _ hu b
      rw [smul_eq_mul, show c * u * b = u * (c * b) by ring]
      exact hu _
  have hin : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
    rintro q -
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨a, ha, j, hj, haj⟩ := Submodule.mem_sup.1 (hb ▸ Submodule.mem_top : (1 : B) ∈ 𝔟 ⊔ I.map (algebraMap A B))
    have : (Submodule.Quotient.mk b : B ⧸ N) = Submodule.Quotient.mk (j * b) := by
      rw [Submodule.Quotient.eq]
      have : b - j * b = a * b := by
        linear_combination (-b) * haj
      rw [this]
      exact 𝔟.mul_mem_right b ha
    rw [this]
    exact key j hj b
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I
    (⊤ : Submodule A (B ⧸ N)) Module.Finite.fg_top hin
  refine ⟨r, hr1, ?_⟩
  have h0 := hr (Submodule.Quotient.mk 1) Submodule.mem_top
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_one] at h0
  exact h0

private theorem nakHom {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B] [Algebra.FiniteType ℂ B]
    (φ : A →ₐ[ℂ] B) (hint : ∀ b : B, φ.toRingHom.IsIntegralElem b) (I : Ideal A) (𝔟 : Ideal B)
    (hb : 𝔟 ⊔ I.map φ.toRingHom = ⊤) : ∃ r : A, r - 1 ∈ I ∧ φ r ∈ 𝔟 := by
  letI alg : Algebra A B := φ.toRingHom.toAlgebra
  haveI tow : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  haveI int : Algebra.IsIntegral A B := ⟨hint⟩
  haveI : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI fin : Module.Finite A B := Algebra.IsIntegral.finite
  exact nakGen I 𝔟 hb

variable {F L : Type} [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L]
  {d : ℕ} (x : Fin (d + 1) → F)

private def tA (j : Fin d) : rA ℂ x {0} :=
  ⟨x j.succ / x 0, Algebra.subset_adjoin ⟨0, Finset.mem_singleton_self 0, j.succ, rfl⟩⟩

private def IA : Ideal (rA ℂ x {0}) := Ideal.span (Set.range (tA x))

private theorem val_one (φ : rA ℂ x {0} →ₐ[ℂ] ℂ) (hφ : ∀ j, φ (tA x j) = 0) {r : rA ℂ x {0}}
    (hr : r - 1 ∈ IA x) : φ r = 1 := by
  have hle : IA x ≤ RingHom.ker φ := by
    rw [IA, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hφ j
  have := hle hr
  rw [RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at this
  exact this

private theorem nak (h : IsFinCover ℂ L x) (𝔟 : Ideal (rB ℂ L x {0}))
    (hb : 𝔟 ⊔ FibFin.coordIdeal ℂ L x = ⊤) :
    ∃ r : rA ℂ x {0}, r - 1 ∈ IA x ∧ FibFin.incl ℂ L x r ∈ 𝔟 := by
  haveI := h.smooth 0
  have hcomp : (rB ℂ L x {0}).val.toRingHom.comp (FibFin.incl ℂ L x).toRingHom =
      algebraMap (rA ℂ x {0}) L := RingHom.ext fun a => rfl
  have hint : ∀ b : rB ℂ L x {0}, (FibFin.incl ℂ L x).toRingHom.IsIntegralElem b := fun b => by
    obtain ⟨p, hpm, hp⟩ : IsIntegral (rA ℂ x {0}) (b : L) := b.2
    refine ⟨p, hpm, ?_⟩
    apply Subtype.ext
    change (rB ℂ L x {0}).val.toRingHom (Polynomial.eval₂ (FibFin.incl ℂ L x).toRingHom b p) = (0 : L)
    rw [Polynomial.hom_eval₂, hcomp]
    exact hp
  have hJ : FibFin.coordIdeal ℂ L x ≤ (IA x).map (FibFin.incl ℂ L x).toRingHom := by
    rw [FibFin.coordIdeal, Ideal.span_le]
    rintro _ ⟨l, rfl⟩
    change (FibFin.incl ℂ L x).toRingHom (tA x l) ∈ _
    exact Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_range_self l))
  exact nakHom (FibFin.incl ℂ L x) hint (IA x) 𝔟 (top_le_iff.1 (hb ▸ sup_le_sup_left hJ 𝔟))

private theorem fib_nonempty (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) : Nonempty (fib ℂ L x) := by
  by_contra hne
  have hall := (FibFin.fib_finite_and_sep ℂ L x h hred).2 1 (fun e => (hne ⟨e⟩).elim)
  have ht : FibFin.coordIdeal ℂ L x = ⊤ := (Ideal.eq_top_iff_one _).2 hall
  obtain ⟨r, hr1, hr⟩ := nak x h ⊥ (by rw [ht]; simp)
  have hr0 : r = 0 := by
    have h0 : algebraMap F L (r : F) = 0 := congrArg Subtype.val ((Ideal.mem_bot).1 hr)
    exact Subtype.ext ((map_eq_zero _).1 h0)
  obtain ⟨e, he⟩ := rA_single_polyEquiv ℂ F d x h.pd 0
  have hε : ((MvPolynomial.aeval (0 : Fin d → ℂ)).comp e.symm.toAlgHom) r = 1 := by
    refine val_one x _ (fun j => ?_) hr1
    have htj : tA x j = e (MvPolynomial.X j) := Subtype.ext (by rw [he j, Fin.succAbove_zero]; rfl)
    rw [htj]
    simp
  rw [hr0, map_zero] at hε
  exact zero_ne_one hε

private theorem comax (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (𝔞 : Ideal (rB ℂ L x {0})) (h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0) :
    𝔞 ⊔ FibFin.coordIdeal ℂ L x = ⊤ := by
  obtain ⟨hfin, hsep⟩ := FibFin.fib_finite_and_sep ℂ L x h hred
  haveI := Fintype.ofFinite (fib ℂ L x)
  classical
  choose b hb hb0 using h𝔞
  choose c hc using fun e0 : fib ℂ L x => hCRT (fun e => if e = e0 then (e0.1 (b e0))⁻¹ else 0)
  have hs : (∑ e0, c e0 * b e0) ∈ 𝔞 := Ideal.sum_mem _ fun e0 _ => 𝔞.mul_mem_left _ (hb e0)
  have hval : ∀ e : fib ℂ L x, e.1 (∑ e0, c e0 * b e0) = 1 := by
    intro e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single e (fun e0 _ hne => by rw [map_mul, hc, if_neg (Ne.symm hne), zero_mul])
      (fun hn => (hn (Finset.mem_univ e)).elim), map_mul, hc, if_pos rfl]
    exact inv_mul_cancel₀ (hb0 e)
  have h1 := hsep (1 - ∑ e0, c e0 * b e0) (fun e => by rw [map_sub, map_one, hval, sub_self])
  rw [Ideal.eq_top_iff_one]
  exact Submodule.mem_sup.2 ⟨_, hs, _, h1, by ring⟩

private theorem partialTrace_valuation_sum (h : IsFinCover ℂ L x)
    (hred : IsReduced (rB ℂ L x {0} ⧸ FibFin.coordIdeal ℂ L x)) (ρ : F →ₗ[ℂ] ℂ)
    (hRT : ∀ b : rB ℂ L x {0}, ρ (Algebra.trace F L b) = ∑ᶠ e : fib ℂ L x, e.1 b)
    (hRes : ∀ e : fib ℂ L x, ∀ f ∈ rA ℂ x {0}, Val (rB ℂ L x {0}) e.1 (algebraMap F L f) (ρ f))
    (hCRT : ∀ v : fib ℂ L x → ℂ, ∃ b : rB ℂ L x {0}, ∀ e : fib ℂ L x, e.1 b = v e)
    (g : L) (γ : fib ℂ L x → ℂ) (hg : ∀ e : fib ℂ L x, Val (rB ℂ L x {0}) e.1 g (γ e))
    (ht : Algebra.trace F L g ∈ rA ℂ x {0}) :
    ρ (Algebra.trace F L g) = ∑ᶠ e, γ e := by
  let 𝔞 : Ideal (rB ℂ L x {0}) :=
    { carrier := {b | (b : L) * g ∈ rB ℂ L x {0}}
      add_mem' := by
        intro a b ha hb
        have := (rB ℂ L x {0}).add_mem ha hb
        simpa [add_mul] using this
      zero_mem' := by simpa using (rB ℂ L x {0}).zero_mem
      smul_mem' := by
        intro c b hb
        have := (rB ℂ L x {0}).mul_mem c.2 hb
        simpa [mul_assoc] using this }
  have h𝔞 : ∀ e : fib ℂ L x, ∃ b ∈ 𝔞, e.1 b ≠ 0 := fun e => by
    obtain ⟨b, hb, hbv, hne, -⟩ := hg e
    exact ⟨⟨b, hb⟩, hbv, hne⟩
  obtain ⟨s, hs1, hs⟩ := nak x h 𝔞 (comax x h hred hCRT 𝔞 h𝔞)
  have hs' : algebraMap F L (s : F) * g ∈ rB ℂ L x {0} := hs
  have hone : ∀ e : fib ℂ L x, e.1 (FibFin.incl ℂ L x s) = 1 := fun e =>
    val_one x (e.1.comp (FibFin.incl ℂ L x)) (fun j => e.2 j) hs1
  have hval : ∀ e : fib ℂ L x, e.1 ⟨_, hs'⟩ = γ e := by
    intro e
    obtain ⟨b, hb, hbv, hne, heq⟩ := hg e
    have h1 : (⟨b, hb⟩ : rB ℂ L x {0}) * ⟨_, hs'⟩ = FibFin.incl ℂ L x s * ⟨b * g, hbv⟩ := by
      apply Subtype.ext
      change b * (algebraMap F L (s : F) * g) = algebraMap F L (s : F) * (b * g)
      ring
    have h2 := congrArg e.1 h1
    rw [map_mul, map_mul, hone, one_mul, heq] at h2
    exact mul_left_cancel₀ hne h2
  obtain ⟨e0⟩ := fib_nonempty x h hred
  have hev : ∀ f : rA ℂ x {0}, e0.1 (FibFin.incl ℂ L x f) = ρ f := by
    intro f
    obtain ⟨b, hb, hbv, hne, heq⟩ := hRes e0 f f.2
    have h1 : (⟨b * algebraMap F L f, hbv⟩ : rB ℂ L x {0}) = ⟨b, hb⟩ * FibFin.incl ℂ L x f := rfl
    rw [h1, map_mul] at heq
    exact mul_left_cancel₀ hne heq
  have htr : Algebra.trace F L (algebraMap F L (s : F) * g) = (s : F) * Algebra.trace F L g := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  have h3 : ρ ((s : F) * Algebra.trace F L g) = ρ (Algebra.trace F L g) := by
    have h4 := hev (s * ⟨_, ht⟩)
    rw [map_mul, map_mul, hone e0, one_mul, hev] at h4
    exact h4.symm
  rw [← h3, ← htr]
  exact (hRT ⟨_, hs'⟩).trans (finsum_congr hval)

end UpperTheory.Gal.productCup_of_system.PartialTraceValue

end

theorem UpperTheory.Gal.productCup_of_system.trVal_of :
    ResidueOfTraceIsFiberSum → ResVal → CRT → ValBasic → TrVal := by
  intro hRT hRes hCRT _ F L _ _ _ _ _ _ d x hc hred ρ hρ g γ hg ht
  exact PartialTraceValue.partialTrace_valuation_sum (xv x) hc hred ρ (hRT F L d x hc hred ρ hρ)
    (fun e f hf => hRes F L d x hc ρ hρ e f hf) (hCRT F L d x hc).2 g γ hg ht
end
