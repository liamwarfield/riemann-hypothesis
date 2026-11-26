module

public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftOfEachRow
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SurjectiveOfLocallySurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycle
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
noncomputable section

namespace GlobalTheory.LocalInv

open NumberField IsDedekindDomain Polynomial Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

abbrev Eig : Type := ∀ w : PlE H, A.LP w → G H.E N.Om → Multiset ℂ

def FrobLift (w : PlE H) (σ : G H.E N.Om) : Prop := IsFrob (F := H.E) (N.plOm.1 w) (normV w) σ

def TemperedSizes (eig : Eig N A) : Prop := ∀ w σ, FrobLift N w σ → ∀ a : A.LP w, A.tempered a →
  ∀ α ∈ eig w a σ, ((normV w : ℕ) : ℝ) ^ (-(((A.lpDim a : ℝ) - 1) / 2)) ≤ ‖α‖ ∧
    ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((A.lpDim a : ℝ) - 1) / 2)

def EtaType : Prop := A.csd A.etaT ∧ ∀ τ, ∀ z ∈ A.infG A.etaT τ, ∃ k : ℤ, z = (k : ℂ) + 1 / 2

def WeightRegular : Prop := ∀ (i : N.Loc) (_ : A.AV i) (τ : H.E →+* ℂ), (A.infWt i τ).Nodup ∧
  ∀ z ∈ A.infWt i τ, ∃ k : ℤ, z = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

def GoodCuspidal : Prop := ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
  HasParamX N A i x Sig → goodSig N A Sig → IsCuspIso N A Sig

theorem weightRegular_of_ext (B : NBC A) : WeightRegular N A := fun i P τ => by
  rw [B.embAV_inf i P]
  exact B.infW_alg _ _ τ

theorem one_lt_normV (w : PlE H) : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by
  have : Finite (𝓞 H.E ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  have : Nontrivial (𝓞 H.E ⧸ w.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr w.isPrime.ne_top
  exact_mod_cast (Finite.one_lt_card : 1 < Nat.card (𝓞 H.E ⧸ w.asIdeal))

theorem normV_ne_zero (w : PlE H) : ((normV w : ℕ) : ℂ) ≠ 0 := by
  have h := one_lt_normV w
  have : (normV w : ℕ) ≠ 0 := by
    intro h0
    rw [h0] at h
    norm_num at h
  exact_mod_cast this

theorem r_odd (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have := R.two_le_m
  exact ⟨a + b - 1, by unfold Ranks.r; omega⟩

theorem r_add_le (R : Ranks) : R.r + 5 ≤ R.t := R.rank_add_five_le

theorem chi_apply (i : N.Loc) (k : ℕ) (hk : k < R.t) (g : G H.E N.Om) :
    N.chi i (k + 1) g = N.chi i 1 g * ((eps N i g) ^ k)⁻¹ := by
  rw [N.chi_def i (k + 1) (by omega) (by omega)]
  simp [eps]

theorem eps_cont (i : N.Loc) : Continuous fun g => ((eps N i g : (N.O i)ˣ) : N.O i) := by
  have h : ∀ g, ((eps N i g : (N.O i)ˣ) : N.O i) =
      ((N.chi i 1 g : (N.O i)ˣ) : N.O i) * ((N.chi i 2 g⁻¹ : (N.O i)ˣ) : N.O i) := by
    intro g
    have := r_add_le R
    rw [← Units.val_mul, chi_apply N i 1 (by omega)]
    simp
  simp only [h]
  exact (N.chi_cont i 1).mul ((N.chi_cont i 2).comp continuous_inv)

theorem iota_eps (i : N.Loc) {w : PlE H} (hw : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    iotaO N A i ((eps N i σ : (N.O i)ˣ) : N.O i) = ((normV w : ℕ) : ℂ) := by
  have h := cycZ_of_isFrob (l := N.l i) hw hB hσ
  have : ((eps N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [this, h]
  simp

theorem galPol_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) :
    galPol A (A.lpSum a b) = galPol A a * galPol A b := by
  unfold galPol
  rw [A.frobEig_sum a b ha hb, Multiset.map_add (f := _), Multiset.prod_add]

theorem galPol_tw_sum {w : PlE H} (a b : A.LP w) (ha : A.unr a) (hb : A.unr b) (s : ℝ) :
    galPol A (A.lpTw (A.lpSum a b) s) = galPol A (A.lpTw a s) * galPol A (A.lpTw b s) := by
  rw [A.lpTw_sum, galPol_sum N A _ _ ((A.unr_tw _ _).2 ha) ((A.unr_tw _ _).2 hb)]

theorem galPol_tw_zero (w : PlE H) (s : ℝ) : galPol A (A.lpTw (A.lpZero w) s) = 1 := by
  unfold galPol
  rw [A.frobEig_tw _ _ (A.lpZero_unr w), A.frobEig_zero]
  simp

theorem galPol_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (e : ℝ → ℝ) (s : ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) ∧
    galPol A (A.lpTw (L.foldr (fun k acc => A.lpSum (A.lpTw a (e k)) acc) (A.lpZero w)) s) =
      (L.map fun k => galPol A (A.lpTw a (e k + s))).prod := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, by simpa using galPol_tw_zero N A w s⟩
  | cons k L ih =>
    refine ⟨(A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 ha, ih.1⟩, ?_⟩
    rw [List.foldr_cons, galPol_tw_sum N A _ _ ((A.unr_tw _ _).2 ha) ih.1, ih.2, A.lpTw_add,
      List.map_cons, List.prod_cons]

theorem list_coe {α β : Type} (f : α → β) (L : List α) :
    (do let a ← L; pure (f a) : List β) = L.map f := by
  induction L with
  | nil => rfl
  | cons a L ih => simpa using ih

theorem galPol_speh (p : Part A.CG) (w : PlE H) (ha : A.unr (A.locG p.π w)) (s : ℝ) :
    A.unr (spehLoc N A p w) ∧ galPol A (A.lpTw (spehLoc N A p w) s) =
      ∏ k ∈ Finset.range p.d, galPol A (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k + s)) := by
  have h := galPol_foldr N A _ ha (fun k => ((p.d : ℝ) - 1) / 2 - k) s
    (do let a ← List.range p.d; pure ((a : ℕ) : ℝ))
  refine ⟨h.1, h.2.trans ?_⟩
  rw [list_coe, List.map_map, ← List.prod_toFinset _ List.nodup_range, List.toFinset_range]
  rfl

theorem galPol_block (i : N.Loc) {w : PlE H} (hw : SplitOut N i w) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) (u : ℝ) :
    galPol A (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w)
      (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2 + u)) =
      X - C (iotaO N A i ((N.chi i 1 σ : (N.O i)ˣ) : N.O i) * ((normV w : ℕ) : ℂ) ^ ((u : ℝ) : ℂ)) := by
  obtain ⟨h1, h2⟩ := A.chi_mu i w hw
  unfold galPol
  rw [← A.lpTw_add, A.frobEig_tw _ _ ((A.unr_tw _ _).2 h1), h2 B σ hB hσ]
  simp [iotaO]

theorem part_alg (hη : EtaType N A) (hW : WeightRegular N A) (i : N.Loc) (P : A.AV i)
    (Pa : List (Part A.CG)) (hB : IsBCV N A i P Pa) (p : Part A.CG) (hp : p ∈ Pa) (ha : Odd p.a)
    (hd : Odd p.d) : A.csd (A.tw p.π A.etaT) ∧ A.ralg (A.tw p.π A.etaT) := by
  refine ⟨A.csd_tw _ _ hη.1 (hB.1 p hp).2.2, (A.ralg_def _).2 fun τ => ?_⟩
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.mp (A.infG_card A.etaT τ)
  obtain ⟨k0, hk0⟩ := hη.2 τ s (by rw [hs]; exact Multiset.mem_singleton_self s)
  have hle : (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - ((0 : ℕ) : ℂ))) ≤ A.infWt i τ := by
    rw [← hB.2.2.2.2.2 τ]
    unfold isoInf
    refine le_trans ?_ (List.single_le_sum (fun _ _ => Multiset.zero_le _) _ (List.mem_map_of_mem hp))
    refine List.single_le_sum (fun _ _ => Multiset.zero_le _) _
      (List.mem_map_of_mem (f := fun k : ℂ => (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))) ?_)
    rw [list_coe]
    exact List.mem_map_of_mem (List.mem_range.mpr hd.pos)
  rw [A.infG_tw _ _ τ s hs]
  refine ⟨(Multiset.Nodup.of_map _ (Multiset.nodup_of_le hle (hW i P τ).1)).map (add_left_injective s), ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hz
  obtain ⟨k, hk⟩ := (hW i P τ).2 _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hy))
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  obtain ⟨r, hr⟩ := r_odd R
  obtain ⟨t, ht⟩ := R.t_odd
  refine ⟨k + k0 + r + t + 1 - d - a, ?_⟩
  rw [Ranks.nV, hr, ht, hd] at hk
  rw [hk0, ha]
  push_cast at hk ⊢
  linear_combination hk

end GlobalTheory.LocalInv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquare
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylRowAll

def coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R) (F : MvPolynomial σ S) :
    MvPolynomial σ R :=
  ∑ m ∈ F.support, monomial m (c (AddMonoidAlgebra.coeff F m))

theorem coeff_coeffMap {R S σ : Type} [CommRing R] [CommRing S] (c : S →+ R)
    (F : MvPolynomial σ S) (m : σ →₀ ℕ) : AddMonoidAlgebra.coeff (coeffMap c F) m = c (AddMonoidAlgebra.coeff F m) := by
  classical
  simp only [coeffMap, coeff_sum, coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem coeffMap_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (c : S →+ R)
    (hc : ∀ (s : S) (a : R), c (s * φ a) = c s * a) {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) S) (hF : F ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν) :
    coeffMap c F ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  have key : ∀ s : S, coeffMap c (s • F) ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
    unfold Formalism.GradedWeylDivisibility.weyl at hF
    induction hF using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      intro s
      have : coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) =
          c s • Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν) := by
        ext m
        rw [coeff_coeffMap, ← Formalism.GradedWeylDivisibility.lclosedeq_hw_map φ, Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map,
          coeff_smul, coeff_smul, coeff_map, smul_eq_mul, smul_eq_mul, hc]
      show coeffMap c (s • Formalism.GradedWeylDivisibility.applyWord S w (Formalism.GradedWeylDivisibility.hw S hn ν)) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩)
    | zero =>
      intro s
      have : coeffMap c (s • (0 : MvPolynomial (Fin r × Fin n) S)) = 0 := by
        ext m; simp [coeff_coeffMap]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      intro s
      have : coeffMap c (s • (x + y)) = coeffMap c (s • x) + coeffMap c (s • y) := by
        ext m; simp [coeff_coeffMap, mul_add]
      rw [this]; exact Submodule.add_mem _ (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [smul_smul]; exact hx _
  simpa using key 1

theorem map_mem_weyl {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ} (hn : n ≤ r)
    (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) :
    map φ f ∈ Formalism.GradedWeylDivisibility.weyl S r n hn ν := by
  unfold Formalism.GradedWeylDivisibility.weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    show map φ (Formalism.GradedWeylDivisibility.applyWord R w (Formalism.GradedWeylDivisibility.hw R hn ν)) ∈ _
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hx

theorem map_rowAct {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (g : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R) :
    map φ (Formalism.GradedWeylDivisibility.rowAct R g f) = Formalism.GradedWeylDivisibility.rowAct S (g.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct]

def toInv (R : Type) [CommRing R] : Polynomial R →+* HahnSeries ℤ R :=
  Polynomial.eval₂RingHom HahnSeries.C (HahnSeries.single (-1 : ℤ) (1 : R))

theorem coeff_zero_toInv (R : Type) [CommRing R] (p : Polynomial R) :
    (toInv R p).coeff 0 = p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial k a =>
    simp only [toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial,
      Polynomial.eval_monomial, HahnSeries.single_pow, HahnSeries.C_apply,
      HahnSeries.single_mul_single]
    rcases k with _ | k
    · simp
    · rw [HahnSeries.coeff_single_of_ne]
      · simp
      · simp; omega

theorem isUnit_shift (R : Type) [CommRing R] {r : ℕ} (M : Matrix (Fin r) (Fin r) R) :
    IsUnit ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) := by
  set A : Matrix (Fin r) (Fin r) (PowerSeries R) :=
    1 + (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C with hA
  have h1 : IsUnit A.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have : (PowerSeries.constantCoeff (R := R)).mapMatrix A = 1 := by
      ext i j
      by_cases h : i = j <;> simp [hA, Matrix.one_apply, h]
    rw [this]; simp
  have h2 : IsUnit (A.map (HahnSeries.ofPowerSeries ℤ R)).det := by
    have := h1.map (HahnSeries.ofPowerSeries ℤ R)
    rwa [RingHom.map_det] at this
  have hT : (HahnSeries.single (-1 : ℤ) (1 : R)) * HahnSeries.single (1 : ℤ) (1 : R) = 1 := by
    rw [HahnSeries.single_mul_single]; simp
  have h3 : ((M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _)).map
      (toInv R)) = (HahnSeries.single (-1 : ℤ) (1 : R)) • A.map (HahnSeries.ofPowerSeries ℤ R) := by
    refine Matrix.ext fun i j => ?_
    simp only [hA, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add (f := _),
      map_mul, HahnSeries.ofPowerSeries_X, HahnSeries.ofPowerSeries_C, mul_add, ← mul_assoc, hT,
      one_mul, toInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X,
      Matrix.one_apply]
    rw [add_comm]
    split_ifs <;> simp
  rw [Matrix.isUnit_iff_isUnit_det, h3, Matrix.det_smul]
  exact ((IsUnit.of_mul_eq_one _ hT).pow _).mul h2

theorem rowAct_mem_weyl (R : Type) [CommRing R] {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (M : Matrix (Fin r) (Fin r) R) (f : MvPolynomial (Fin r × Fin n) R)
    (hf : f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν) : Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R r n hn ν := by
  set B : Matrix (Fin r) (Fin r) (Polynomial R) :=
    M.map Polynomial.C + (Polynomial.X : Polynomial R) • (1 : Matrix (Fin r) (Fin r) _) with hB
  obtain ⟨u, hu⟩ := isUnit_shift R M
  have h1 := Formalism.UG.Final.WeylGLStable (HahnSeries ℤ R) r n hn ν u⁻¹ _
    (map_mem_weyl (toInv R) hn ν _ (map_mem_weyl Polynomial.C hn ν f hf))
  rw [Formalism.UG.dwAct, inv_inv, hu, ← hB, ← map_rowAct] at h1
  have h2 := coeffMap_mem_weyl (HahnSeries.C : R →+* HahnSeries ℤ R)
    (HahnSeries.coeff.addMonoidHom (0 : ℤ)) (by
      intro s a
      simp [HahnSeries.C_apply, HahnSeries.coeff_mul_single_zero]) hn ν _ h1
  have h3 : coeffMap (HahnSeries.coeff.addMonoidHom (0 : ℤ))
      (map (toInv R) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f))) =
      map (Polynomial.evalRingHom (0 : R)) (Formalism.GradedWeylDivisibility.rowAct (Polynomial R) B (map Polynomial.C f)) := by
    ext m
    rw [coeff_coeffMap, coeff_map, coeff_map]
    exact coeff_zero_toInv R _
  have h4 : B.map (Polynomial.evalRingHom (0 : R)) = M := by
    ext i j
    simp [hB]
  have h5 : map (Polynomial.evalRingHom (0 : R)) (map Polynomial.C f) = f := by
    ext m
    simp [coeff_map]
  rwa [h3, map_rowAct, h4, h5] at h2

theorem rowAct_mem_weyl_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν →
    ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν,
      Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν :=
  fun R _ _ ν _ M f hf => rowAct_mem_weyl R le_rfl ν M f hf

end GlobalTheory.WeylRowAll
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeylRowActionMemWeylLatticeSquareStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weylRowAction_mem_weylLattice_square : ∀ (R : Type) [CommRing R] (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∀ (M : Matrix (Fin n) (Fin n) R), ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν, Formalism.GradedWeylDivisibility.rowAct R M f ∈ Formalism.GradedWeylDivisibility.weyl R n n le_rfl ν := by
  first | exact @GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | exact GlobalTheory.WeylRowAll.rowAct_mem_weyl_square | (intros; apply GlobalTheory.WeylRowAll.rowAct_mem_weyl_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducible
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SemisimpleDecomp

variable {k Γ : Type} [Field k] [Group Γ] {a : ℕ}

theorem isInv_inf {ρ : Γ →* GL (Fin a) k} {U V : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (hV : IsInv ρ V) : IsInv ρ (U ⊓ V) :=
  fun g v hv => ⟨hU g v hv.1, hV g v hv.2⟩

theorem isInv_top (ρ : Γ →* GL (Fin a) k) : IsInv ρ ⊤ := fun _ _ _ => Submodule.mem_top

theorem exists_irr_le {ρ : Γ →* GL (Fin a) k} {U : Submodule k (Fin a → k)} (hU : IsInv ρ U)
    (h0 : U ≠ ⊥) : ∃ W, W ≤ U ∧ IsIrrSub ρ W := by
  obtain ⟨W, ⟨hW0, hWi, hWU⟩, hmin⟩ := (wellFounded_lt (α := Submodule k (Fin a → k))).has_min
    {W | W ≠ ⊥ ∧ IsInv ρ W ∧ W ≤ U} ⟨U, h0, hU, le_rfl⟩
  refine ⟨W, hWU, hW0, hWi, fun W' hle hi => ?_⟩
  by_cases h : W' = ⊥
  · exact Or.inl h
  · right
    by_contra hne
    exact hmin W' ⟨h, hi, hle.trans hWU⟩ (lt_of_le_of_ne hle hne)

theorem disjoint_sup_of_le {α : Type*} [Lattice α] [OrderBot α] [IsModularLattice α] {x b c w : α}
    (hx : x ≤ c) (hb : b ≤ c) (hxb : Disjoint x b) (hw : Disjoint w c) : Disjoint x (w ⊔ b) := by
  have hc : (b ⊔ w) ⊓ c = b := by
    rw [sup_inf_assoc_of_le w hb, hw.eq_bot, sup_bot_eq]
  rw [disjoint_iff_inf_le]
  calc x ⊓ (w ⊔ b) ≤ x ⊓ b := by
        refine le_inf inf_le_left ?_
        exact (le_inf (inf_le_right.trans (sup_comm w b).le) (inf_le_left.trans hx)).trans hc.le
    _ ≤ ⊥ := hxb.le_bot

theorem exists_decomp {ρ : Γ →* GL (Fin a) k} (hρ : IsSSRep ρ) (U : Submodule k (Fin a → k))
    (hU : IsInv ρ U) : ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      iSupIndep Vs ∧ iSup Vs = U ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  induction U using WellFoundedLT.induction with
  | _ U ih =>
  by_cases h0 : U = ⊥
  · exact ⟨0, Fin.elim0, fun i => i.elim0, by simp [h0], fun j => j.elim0⟩
  obtain ⟨W, hWU, hW⟩ := exists_irr_le hU h0
  obtain ⟨W', hW'i, hc⟩ := hρ W hW.2.1
  have hlt : U ⊓ W' < U := by
    refine lt_of_le_of_ne inf_le_left fun heq => hW.1 ?_
    have hle : W ≤ W' := hWU.trans (heq.symm ▸ inf_le_right)
    exact hc.disjoint.eq_bot_of_le hle
  obtain ⟨n, Vs, hind, hsup, hirr⟩ := ih _ hlt (isInv_inf hU hW'i)
  have hVs : ∀ j, Vs j ≤ U ⊓ W' := fun j => hsup ▸ le_iSup Vs j
  refine ⟨n + 1, Fin.cons W Vs, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · refine hc.disjoint.mono_right (iSup₂_le fun j hj => ?_)
      refine Fin.cases (fun h => absurd rfl h) (fun j _ => ?_) j hj
      simpa using (hVs j).trans inf_le_right
    · have hle : (⨆ (j) (_ : j ≠ Fin.succ i), (Fin.cons W Vs : Fin (n + 1) → _) j) ≤
          W ⊔ ⨆ (j) (_ : j ≠ i), Vs j := by
        refine iSup₂_le fun j hj => ?_
        refine Fin.cases (fun _ => ?_) (fun j hj => ?_) j hj
        · simp
        · have hji : j ≠ i := fun h => hj (h ▸ rfl)
          simp only [Fin.cons_succ]
          exact le_sup_of_le_right (le_iSup₂ (f := fun j (_ : j ≠ i) => Vs j) j hji)
      simp only [Fin.cons_succ]
      refine (disjoint_sup_of_le (hVs i) (iSup₂_le fun j _ => hVs j) (hind i)
        (hc.disjoint.mono_right inf_le_right)).mono_right hle
  · have hS : iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) = W ⊔ iSup Vs := by
      refine le_antisymm (iSup_le fun j => ?_) (sup_le ?_ (iSup_le fun j => ?_))
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp
        · simpa using le_sup_of_le_right (le_iSup Vs j)
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) 0
      · simpa using le_iSup (Fin.cons W Vs : Fin (n + 1) → Submodule k (Fin a → k)) j.succ
    rw [hS, hsup, inf_comm, ← sup_inf_assoc_of_le W' hWU, hc.sup_eq_top, top_inf_eq]
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hW
    · simpa using hirr j

end GlobalTheory.SemisimpleDecomp

theorem GlobalTheory.semisimple_matrix_rep_decomp : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ}
    (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)),
      DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  intro k Γ _ _ a ρ hρ
  obtain ⟨n, Vs, hind, hsup, hirr⟩ :=
    GlobalTheory.SemisimpleDecomp.exists_decomp hρ ⊤ (GlobalTheory.SemisimpleDecomp.isInv_top ρ)
  exact ⟨n, Vs, (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top Vs).2 ⟨hind, hsup⟩,
    hirr⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleMatrixRepIsInternalIrreducibleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_matrixRep_isInternal_irreducible : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k), IsSSRep ρ → ∃ (n : ℕ) (Vs : Fin n → Submodule k (Fin a → k)), DirectSum.IsInternal Vs ∧ ∀ j, IsIrrSub ρ (Vs j) := by
  first | exact @GlobalTheory.semisimple_matrix_rep_decomp | exact GlobalTheory.semisimple_matrix_rep_decomp | (intros; apply GlobalTheory.semisimple_matrix_rep_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RiemannFormHermitianLattice
open KaehlerDifferential GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PD

theorem mOm_ιMulti_D_algebraMap (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] (q : ℕ) (w : Fin q → A) :
    ((semiHom_algebraMap k A K).mOm q (exteriorPower.ιMulti A q fun j => D k A (w j)) : DR k K) =
      ExteriorAlgebra.ιMulti K q fun j => D k K (algebraMap A K (w j)) := by
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (SemiHom.mDR_ι _ _).trans (congrArg _ (SemiHom.m1_D _ _))

theorem mOm_injective_and_omB (k K A : Type) [Field k] [Field K] [Algebra k K] [CommRing A]
    [Algebra k A] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K] [Algebra.Smooth k A]
    (B : Subalgebra k K) (hB : ∀ y, y ∈ B ↔ ∃ f : A, algebraMap A K f = y) (q : ℕ) :
    Function.Injective ((semiHom_algebraMap k A K).mOm q) ∧
      ∀ y : DR k K, y ∈ omB k K B q ↔
        ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y := by
  haveI : IsDomain A := (IsFractionRing.injective A K).isDomain (algebraMap A K)
  haveI : Algebra.FormallyEtale A K := .of_isLocalization (nonZeroDivisors A)
  have hE : IsLocalizedModule (nonZeroDivisors A) (formLin k A K q) :=
    (isLocalizedModule_iff_isBaseChange _ K _).2 (isBaseChange_formLin k A K q)
  haveI : Module.Projective A (⋀[A]^q Ω[A⁄k]) := by
    obtain ⟨s, hs⟩ := Module.projective_def'.1 (inferInstance : Module.Projective A Ω[A⁄k])
    exact Module.Projective.of_split (exteriorPower.map q s)
      (exteriorPower.map q (Finsupp.linearCombination A id))
      (by rw [← exteriorPower.map_comp, hs, exteriorPower.map_id])
  haveI : Module.Flat A (⋀[A]^q Ω[A⁄k]) := inferInstance
  haveI : Module.IsTorsionFree A (⋀[A]^q Ω[A⁄k]) := Module.Flat.isTorsionFree
  have hinj : Function.Injective (formLin k A K q) := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors A) hxy
    exact (Module.IsTorsionFree.isSMulRegular (M := ⋀[A]^q Ω[A⁄k])
      (isRegular_iff_ne_zero.mpr (nonZeroDivisors.coe_ne_zero c))) hc
  have hsm : ∀ (a : A) (z : Om k A q), ((semiHom_algebraMap k A K).mOm q (a • z) : DR k K) =
      algebraMap A K a • ((semiHom_algebraMap k A K).mOm q z : DR k K) := fun a z => by
    rw [SemiHom.mOm_smul]; rfl
  refine ⟨hinj, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · let S : Submodule k (DR k K) :=
      { carrier := {y | ∃ z : Om k A q, ((semiHom_algebraMap k A K).mOm q z : DR k K) = y}
        add_mem' := by
          rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
          exact ⟨a + b, by rw [map_add (f := _)]; rfl⟩
        zero_mem' := ⟨0, by rw [map_zero]; rfl⟩
        smul_mem' := by
          rintro c _ ⟨a, rfl⟩
          refine ⟨algebraMap k A c • a, ?_⟩
          rw [hsm, ← IsScalarTower.algebraMap_apply, algebraMap_smul] }
    have : omB k K B q ≤ S := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨b, hb, v, hv, rfl⟩
      obtain ⟨a, rfl⟩ := (hB b).1 hb
      choose w hw using fun j => (hB (v j)).1 (hv j)
      refine ⟨a • exteriorPower.ιMulti A q (fun j => D k A (w j)), ?_⟩
      rw [hsm, mOm_ιMulti_D_algebraMap]
      simp only [hw]
    exact this hy
  · rintro ⟨z, rfl⟩
    have htop := exteriorPower.ιMulti_span_of_span A q Ω[A⁄k] (span_range_derivation k A)
    have hz : z ∈ Submodule.span A
        (⇑(exteriorPower.ιMulti A q) '' {a | Set.range a ⊆ Set.range (D k A)}) := by
      rw [htop]; exact Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, rfl⟩ := hz
      choose w hw using fun j => ha ⟨j, rfl⟩
      have ha' : a = fun j => D k A (w j) := funext fun j => (hw j).symm
      subst ha'
      rw [mOm_ιMulti_D_algebraMap]
      exact ιMulti_D_mem_omB_regForms B q fun j => ⟨algebraMap A K (w j), (hB _).2 ⟨w j, rfl⟩⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _)]; exact add_mem h1 h2
    | smul a z _ h => rw [hsm]; exact smul_mem_omB_regForms B q ((hB _).2 ⟨a, rfl⟩) h

end GlobalTheory.PD
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsoLocAppendSingleton
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaEigenspaceImage
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage

open Formalism.BasicNotions Formalism.MainNotions.N

def ThetaTMapsIntoEig {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSig N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

def MjSigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w}, what₂.isot (N.j i) σ

def ThetaTMapsIntoEigOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
    x ∈ ZgoodN N A i → HasParamX N A i x Sig →
      ∀ f ∈ MjSigOut N A i Sig, what₂.thetaT (N.mu i) (N.j i) f ∈ eigC N A i x

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem mjSig_le_mjSigOut (i : N.Loc) (Sig : List (Part A.CG)) :
    MjSig N A i Sig ≤ MjSigOut N A i Sig := by
  unfold MjSig MjSigOut
  exact biSup_mono fun σ hσ w hw => hσ.2.2 w hw.1

theorem thetaTMapsIntoEig_of_out (h : ThetaTMapsIntoEigOut N A) : ThetaTMapsIntoEig N A :=
  fun i x Sig hx hp f hf => h i x Sig hx hp f (mjSig_le_mjSigOut N A i Sig hf)

theorem thetaTMapsIntoEig_iff_map_le : ThetaTMapsIntoEig N A ↔
    ∀ (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)),
      x ∈ ZgoodN N A i → HasParamX N A i x Sig →
        (MjSig N A i Sig).map (what₂.thetaT (N.mu i) (N.j i)) ≤ eigC N A i x := by
  unfold ThetaTMapsIntoEig
  simp only [Submodule.map_le_iff_le_comap]
  rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage
end
end

noncomputable section

namespace GlobalTheory.ParUpRoad

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh GlobalTheory.IndefiniteRowSideFullHecke.ThetaEigenspaceImage GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftOfEachComponent

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_twist (hL : ParamLaws N A) (p : Part A.CG) (χ : A.CG 1) (w : PlE H) :
    spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w = A.lpChar (spehLoc N A p w) (A.locG χ w) := by
  obtain ⟨hsum, hzero, htw, -, -⟩ := hL w
  have hχ := A.locG_dim χ w
  unfold spehLoc
  dsimp only
  generalize (List.range p.d >>= fun a : ℕ => (pure (a : ℝ) : List ℝ)) = l
  induction l with
  | nil => exact (hzero _ hχ).symm
  | cons k l ih =>
    rw [List.foldr_cons, List.foldr_cons, ih, hsum _ _ _ hχ, htw _ _ _ hχ, A.locG_tw]

theorem isoLoc_twist (hL : ParamLaws N A) (S : List (Part A.CG)) (χ : A.CG 1) (w : PlE H) :
    isoLoc N A (twistIso N A S χ) w = A.lpChar (isoLoc N A S w) (A.locG χ w) := by
  have hχ := A.locG_dim χ w
  induction S with
  | nil => exact ((hL w).2.1 _ hχ).symm
  | cons p S ih =>
    change A.lpSum (spehLoc N A ⟨p.a, A.tw p.π χ, p.d⟩ w) (isoLoc N A (twistIso N A S χ) w) =
      A.lpChar (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (A.locG χ w)
    rw [ih, spehLoc_twist N A hL, (hL w).1 _ _ _ hχ]

theorem isoLoc_append_singleton (S : List (Part A.CG)) (q : Part A.CG) (w : PlE H) :
    isoLoc N A (S ++ [q]) w = A.lpSum (isoLoc N A S w) (spehLoc N A q w) := by
  induction S with
  | nil =>
    change A.lpSum (spehLoc N A q w) (A.lpZero w) = A.lpSum (A.lpZero w) (spehLoc N A q w)
    exact A.lpSum_comm _ _
  | cons p S ih =>
    change A.lpSum (spehLoc N A p w) (isoLoc N A (S ++ [q]) w) =
      A.lpSum (A.lpSum (spehLoc N A p w) (isoLoc N A S w)) (spehLoc N A q w)
    rw [ih, A.lpSum_assoc]

theorem isoLoc_lift (hL : ParamLaws N A) (i : N.Loc) (Sig : List (Part A.CG)) (w : PlE H) :
    isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w =
      liftPar N A i w (isoLoc N A Sig w) := by
  rw [isoLoc_twist N A hL, isoLoc_append_singleton]
  rfl

theorem ptV_of_thetaOf (hL : ParamLaws N A) {i : N.Loc} (hS : SplitLift N A i) (hP : PtOfLoc N A i)
    {x : N.X i} {Sig : List (Part A.CG)} (hx : HasParamX N A i x Sig) {σ : what₂.FT}
    (hσ : ∀ w, SplitOut N i w → isoLoc N A Sig w = A.locW i σ w) {P : A.AV i}
    (hθ : thetaOf N A i σ P) : A.ptV i P = some x := by
  obtain ⟨P', hP', hbc⟩ := hx
  refine hP P P' x hP' fun w hw => ?_
  rw [hS σ P hθ w hw.1, ← hσ w hw, ← isoLoc_lift N A hL, hbc.2.2.2.1 w hw.1]

theorem thetaTMapsIntoEigOut (hθ : EachRowHasThetaLift N A) (hL : ParamLaws N A)
    (hS : ∀ i, SplitLift N A i) (hP : ∀ i, PtOfLoc N A i) : ThetaTMapsIntoEigOut N A := by
  intro i x Sig _ hx
  have key : MjSigOut N A i Sig ≤ (eigC N A i x).comap (what₂.thetaT (N.mu i) (N.j i)) := by
    unfold MjSigOut
    refine iSup₂_le fun σ hσ => ?_
    by_cases h0 : what₂.isot (N.j i) σ = ⊥
    · rw [h0]; exact bot_le
    obtain ⟨P, hPθ⟩ := hθ i σ h0
    have hpt : A.ptV i P = some x := ptV_of_thetaOf N A hL (hS i) (hP i) hx hσ hPθ
    rw [← Submodule.map_le_iff_le_comap]
    refine hPθ.2.trans ?_
    unfold eigC
    exact le_iSup₂_of_le (f := fun P (_ : P ∈ {P | A.ptV i P = some x}) => A.typeV i P) P hpt le_rfl
  exact fun f hf => key hf

theorem main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
    EachRowHasThetaLift N A → ParamLaws N A → (∀ i, SplitLift N A i) → (∀ i, PtOfLoc N A i) →
      ThetaTMapsIntoEig N A :=
  fun _ _ _ N A hθ hL hS hP => thetaTMapsIntoEig_of_out N A (thetaTMapsIntoEigOut N A hθ hL hS hP)

end GlobalTheory.ParUpRoad
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweThetaLiftComponents
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftUniqueness
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness

open Formalism.BasicNotions Formalism.MainNotions.N

def EachRowHasThetaLift {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
    (A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT), what₂.isot (N.j i) σ ≠ ⊥ → ∃ P : A.AV i, thetaOf N A i σ P

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem eachRowHasThetaLift_iff :
    EachRowHasThetaLift N A ↔
      ∀ (i : N.Loc) (σ : what₂.FT), (∃ f ∈ what₂.isot (N.j i) σ, f ≠ 0) → ∃ P : A.AV i,
        (∃ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ≠ 0) ∧
        ∀ f ∈ what₂.isot (N.j i) σ, what₂.thetaT (N.mu i) (N.j i) f ∈ A.typeV i P := by
  unfold EachRowHasThetaLift thetaOf
  refine forall_congr' fun i => forall_congr' fun σ => ?_
  rw [Submodule.ne_bot_iff]
  refine imp_congr_right fun _ => exists_congr fun P => and_congr ?_ ?_
  · rw [Submodule.ne_bot_iff]
    constructor
    · rintro ⟨_, ⟨f, hf, rfl⟩, h⟩
      exact ⟨f, hf, h⟩
    · rintro ⟨f, hf, h⟩
      exact ⟨_, ⟨f, hf, rfl⟩, h⟩
  · rw [Submodule.map_le_iff_le_comap]
    rfl

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaGramMatrix
namespace GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix

open Formalism.BasicNotions Formalism.MainNotions.N

noncomputable def thetaGram {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    what₂.Mj j →ₗ[ℂ] what₂.Mj j :=
  what₂.thetaP μ j ∘ₗ what₂.thetaT μ j

def ThetaGramPositiveScalar {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) (_A : NAut N) : Prop :=
  ∀ (i : N.Loc) (σ : what₂.FT),
    (∀ f ∈ what₂.isot (N.j i) σ,
      thetaGram what₂ (N.mu i) (N.j i) f = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) • f) ∧
    (what₂.isot (N.j i) σ ≠ ⊥ → 0 < what₂.lamP (N.mu i) (N.j i) σ)

theorem ThetaGramPositiveScalar.norm_sq {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ) :
    ‖what₂.thetaT (N.mu i) (N.j i) f‖ ^ 2 = what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 := by
  have hg := (h i σ).1 f hf
  simp only [thetaGram, LinearMap.comp_apply] at hg
  have key : inner ℂ (what₂.thetaT (N.mu i) (N.j i) f) (what₂.thetaT (N.mu i) (N.j i) f)
      = ((what₂.lamP (N.mu i) (N.j i) σ : ℝ) : ℂ) * inner ℂ f f := by
    show inner ℂ (LinearMap.adjoint (what₂.thetaP (N.mu i) (N.j i)) f)
      (what₂.thetaT (N.mu i) (N.j i) f) = _
    rw [LinearMap.adjoint_inner_left, hg, inner_smul_right]
  rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, key]
  simp

theorem ThetaGramPositiveScalar.eq_zero {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} {A : NAut N} (h : ThetaGramPositiveScalar N A) (i : N.Loc) (σ : what₂.FT)
    (f : what₂.Mj (N.j i)) (hf : f ∈ what₂.isot (N.j i) σ)
    (h0 : what₂.thetaT (N.mu i) (N.j i) f = 0) : f = 0 := by
  by_contra hne
  have hpos : 0 < what₂.lamP (N.mu i) (N.j i) σ := by
    apply (h i σ).2
    intro hb
    rw [hb] at hf
    exact hne ((Submodule.mem_bot ℂ).1 hf)
  have e := h.norm_sq i σ f hf
  rw [h0, norm_zero] at e
  have e2 : what₂.lamP (N.mu i) (N.j i) σ * ‖f‖ ^ 2 = 0 := by rw [← e]; norm_num
  rcases mul_eq_zero.1 e2 with h1 | h1
  · exact absurd h1 hpos.ne'
  · exact hne (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h1))

end GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix
end

noncomputable section

namespace GlobalTheory.Proof.HoweThetaLiftComponents

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

theorem mem_of_orthogonal_others {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (p : ι) (horth : ∀ k, k ≠ p → U k ⟂ U p)
    (x : V) (hx : ∀ k, k ≠ p → ∀ y ∈ U k, inner ℂ y x = 0) : x ∈ U p := by
  have hsup : U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    by_cases hk : k = p
    · subst hk; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ p}) => U k) k hk le_rfl)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : x ∈ U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k))
  have hle : (⨆ k ∈ {k | k ≠ p}, U k) ≤ (ℂ ∙ v)ᗮ := by
    refine iSup₂_le fun k hk y hy => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hv' : v = x - u := by rw [← huv]; abel
    rw [hv', inner_sub_right, hx k hk y hy, (horth k hk).inner_eq hy hu, sub_zero]
  have h0 : inner ℂ v v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hv)
  rw [inner_self_eq_zero] at h0
  rw [← huv, h0, add_zero]
  exact hu

theorem exists_inner_ne_zero {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ k, ∃ y ∈ U k, inner ℂ y x ≠ 0 := by
  by_contra h
  push Not at h
  have hle : (⨆ k, U k) ≤ (ℂ ∙ x)ᗮ := iSup_le fun k y hy =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h k y hy)
  rw [htop] at hle
  exact hx (inner_self_eq_zero.1
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (Submodule.mem_top : x ∈ ⊤))))

theorem eachRowHasThetaLift_of_howe :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix.ThetaGramPositiveScalar N A → (∀ i, HoweUp N A i) →
      (∀ i, TypeOrth N A i) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.EachRowHasThetaLift N A := by
  intro R H what₂ N A hpos hhowe horth
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.eachRowHasThetaLift_iff]
  rintro i σ ⟨f, hf, hf0⟩
  have hθ : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (hpos.eq_zero i σ f hf h)
  obtain ⟨P, F, hF, hFf⟩ := exists_inner_ne_zero (A.typeV i) (A.typeV_top i) _ hθ
  refine ⟨P, ⟨f, hf, hθ⟩, fun g hg => ?_⟩
  refine mem_of_orthogonal_others (A.typeV i) (A.typeV_top i) P (fun k hk => horth i k P hk) _
    fun k hk y hy => ?_
  by_contra hne
  exact hk (hhowe i σ k P ⟨g, hg, y, hy, hne⟩ ⟨f, hf, F, hF, hFf⟩)

end GlobalTheory.Proof.HoweThetaLiftComponents
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlgebraMapSecEq
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeCoh

open GlobalTheory.CatCoh GlobalTheory.CechDR

variable {k : Type} [CommRing k] {X X' : Scheme.{0}}

theorem algebraMap_sec_eq (s : X ⟶ Sp k) (U : X.Opens) (r : k) :
    letI := algΓ s
    algebraMap k (Sec s U) r = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) := rfl

theorem toOm_smul_k (s : X ⟶ Sp k) (q : ℕ) (U : X.Opens) (r : k) (x : OmU s U q) :
    letI := algΓ s
    toOm s q U (r • x) = restrictGlobal X U (algebraMap k Γ(X, ⊤) r) • toOm s q U x := by
  letI := algΓ s
  rw [algebra_compatible_smul (Sec s U) r x, map_smul, algebraMap_sec_eq]
  rfl

def omSecEquiv (s : X ⟶ Sp k) (q : ℕ) (U : X.affineOpens) :
    letI := algΓ s
    OmU s U.1 q ≃ₗ[k] sectionsOn (Omega s q) U.1 :=
  letI := algΓ s
  { (toOmEquiv s q U.2).toAddEquiv.trans (sectionsOn.toΓ (Omega s q) U.1).symm with
    map_smul' := fun r x ↦ (sectionsOn.toΓ (Omega s q) U.1).injective (by
      change toOm s q U.1 (r • x) = _
      rw [toOm_smul_k, sectionsOn.toΓ_smul]
      rfl) }

section Pair

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

end Pair

section PairSec

variable {s : X ⟶ Sp k} {s' : X' ⟶ Sp k} {f : X' ⟶ X}

end PairSec

end GlobalTheory.HodgeCoh
end
end
