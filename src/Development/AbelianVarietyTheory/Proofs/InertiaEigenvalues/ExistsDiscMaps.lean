module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsIterateDerivative
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIrrHarishChandraInductionThetaInvDet

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHom
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem breuilKisinDatum_radius_pow_degree_eq_inv {K : FinExt l} (bk : BK K) : bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  have he : (bk.Ep.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.2 bk.deg_pos.ne'
  unfold BK.ρ₀
  rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, neg_mul, one_div, inv_mul_cancel₀ he, NNReal.rpow_neg_one]

theorem breuilKisinDatum_radius_le_one {K : FinExt l} (bk : BK K) : bk.ρ₀ ≤ 1 := by
  unfold BK.ρ₀
  exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hl.out.one_lt.le)
    (neg_nonpos.2 (by positivity))

theorem breuilKisinDatum_radius_pos {K : FinExt l} (bk : BK K) : 0 < bk.ρ₀ := by
  unfold BK.ρ₀
  exact NNReal.rpow_pos (by exact_mod_cast hl.out.pos)

theorem inv_le_rho {K : FinExt l} (bk : BK K) {ρ : ℝ≥0} (h : bk.ρ₀ ≤ ρ) : (l : ℝ≥0)⁻¹ ≤ ρ := by
  rw [← breuilKisinDatum_radius_pow_degree_eq_inv]
  exact (pow_le_of_le_one (by positivity) (breuilKisinDatum_radius_le_one bk) bk.deg_pos.ne').trans h

theorem E_eq {K : FinExt l} (bk : BK K) : ∃ q : bk.S, bk.E = X ^ bk.Ep.natDegree + (l : bk.S) * q := by
  have hm : bk.Ep - Polynomial.X ^ bk.Ep.natDegree ∈ (Ideal.span {(l : Wq l bk.a)}).map Polynomial.C := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy n bk.Ep.natDegree with hn | hn | hn
    · rw [if_neg hn.ne, sub_zero]
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · subst hn
      rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact zero_mem _
    · rw [if_neg hn.ne', Polynomial.coeff_eq_zero_of_natDegree_lt hn, sub_zero]; exact zero_mem _
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hm
  obtain ⟨q, hq⟩ := hm
  refine ⟨(q : bk.S), ?_⟩
  have h1 : bk.Ep = Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q := by
    rw [← hq]; ring
  have h2 : (bk.Ep : bk.S) =
      ((Polynomial.X ^ bk.Ep.natDegree + Polynomial.C (l : Wq l bk.a) * q : Polynomial (Wq l bk.a)) : bk.S) :=
    congrArg _ h1
  show (bk.Ep : bk.S) = _
  rw [h2, Polynomial.coe_add, Polynomial.coe_pow, Polynomial.coe_X, Polynomial.coe_mul, Polynomial.coe_C, map_natCast]

theorem gauge_mono_le {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (a b : ℕ) {r : ℝ} (hr : 0 < r)
    (h : (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a) :
    ‖algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b)‖ ≤ r :=
  gauge_le l u ρ hr (Submodule.subset_span ⟨a, b, 0, by simpa using h, by simp⟩)

end GlobalTheory.BSP.DiscPrism

namespace GlobalTheory.BSP.DiscPrism

variable {l : ℕ} [hl : Fact l.Prime]

theorem norm_toDisc_hf_le {K : FinExt l} (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0)
    (h0 : bk.ρ₀ ≤ ρ) (h1 : ρ ≤ 1) : ‖toDisc l (BK.hf f X) ρ (BK.hf g X)‖ ≤ ρ := by
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 ((breuilKisinDatum_radius_pos bk).trans_le h0)
  have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast h1
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  have hlρ : (1 : ℝ) ≤ ρ * l := by
    have h := inv_le_rho bk h0
    have h' : ((l : ℝ))⁻¹ ≤ ρ := by exact_mod_cast h
    rw [inv_le_iff_one_le_mul₀ hl0] at h'
    linarith [mul_comm (l : ℝ) ρ]
  set u := BK.hf f X with hu
  let am := algebraMap B.A (PreDisc l u ρ)
  have um : ∀ x y : PreDisc l u ρ, ‖x + y‖ ≤ max ‖x‖ ‖y‖ := gauge_add_le_max l u ρ
  have hX : ‖am u‖ ≤ ρ := by
    simpa using gauge_mono_le (l := l) u ρ 0 1 hρ (by simp)
  have hE : ‖am (BK.hf f bk.E)‖ ≤ ρ := by
    obtain ⟨q, hq⟩ := E_eq bk
    have e1 : BK.hf f bk.E = u ^ bk.Ep.natDegree + (l : B.A) ^ 1 * u ^ 0 * BK.hf f q := by
      rw [hq, map_add (f := _), map_pow, map_mul, map_natCast, hu]; ring
    rw [e1, map_add (f := _), map_mul]
    refine (um _ _).trans (max_le ?_ ?_)
    · have := gauge_mono_le (l := l) u ρ 0 bk.Ep.natDegree hρ
        (by simpa using pow_le_of_le_one hρ.le hρ1 bk.deg_pos.ne')
      simpa using this
    · refine (norm_mul_le _ _).trans ?_
      have h2 := gauge_mono_le (l := l) u ρ 1 0 hρ (by simpa using hlρ)
      have h3 := norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (BK.hf f q)
      calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul h2 h3 (norm_nonneg _) hρ.le
        _ = ρ := mul_one _
  have hmem : BK.hf g X - BK.hf f X ∈ B.I := by
    have hs : Ideal.Quotient.mk bk.prism.I (X : bk.S) = bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ X)) :=
      (bk.str.apply_symm_apply _).symm
    exact Ideal.Quotient.eq.1 ((g.f_str _ _ hs).trans (f.f_str _ _ hs).symm)
  have hI : B.I = Ideal.span {BK.hf f bk.E} := by
    rw [← GlobalTheory.T.prism_hom_map_ideal_eq l ↥(OL K) bk.prism B f]
    show (Ideal.span {bk.E}).map (BK.hf f) = _
    rw [Ideal.map_span, Set.image_singleton]
  rw [hI, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have e2 : BK.hf g X = u + BK.hf f bk.E * c := by rw [← hc, hu]; ring
  show ‖ofPre l u ρ (am (BK.hf g X))‖ ≤ ρ
  rw [norm_ofPre, ← norm_preDisc, e2, map_add (f := _), map_mul]
  refine (um _ _).trans (max_le hX ?_)
  refine (norm_mul_le _ _).trans ?_
  calc _ ≤ (ρ : ℝ) * 1 := mul_le_mul hE (norm_algebraMap_le _) (norm_nonneg _) hρ.le
    _ = ρ := mul_one _

theorem disc_map_exists : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 →
    ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  intro l _ K bk B f g ρ h0 h1
  exact ⟨Disc.map (BK.hf g) (norm_toDisc_hf_le bk B f g ρ h0 h1), isDiscMap_map _ _⟩

end GlobalTheory.BSP.DiscPrism
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClosedDiscExtensionBreuilKisinHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F := by
  first | exact @GlobalTheory.BSP.DiscPrism.disc_map_exists | exact GlobalTheory.BSP.DiscPrism.disc_map_exists | (intros; apply GlobalTheory.BSP.DiscPrism.disc_map_exists <;> assumption)
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_discMaps : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ (A A' : Type) [CommRing A] [CommRing A'] (f : A →+* A') (u : A) (u' : A') (ρ ρ' : ℝ≥0) (k : ℕ), 0 < ρ' → u' ^ k ∣ f u → ρ' ^ k ≤ ρ → ∃ F : Disc l u ρ →+* Disc l u' ρ', IsDiscMap (l := _) (u := _) (ρ := _) f F) ∧ (∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l, ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G) ∧ (∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (ρ : ℝ≥0), bk.ρ₀ ≤ ρ → ρ ≤ 1 → ∃ F : bk.DS ρ →+* Disc l (BK.hf f X) ρ, IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf g) F) ∧ 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ bk.ρ₀ ^ bk.Ep.natDegree = (l : ℝ≥0)⁻¹ := by
  intro l _ K bk
  exact ⟨GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l, (GlobalTheory.T.galois_action_extends_to_ainf_disc_rings l K bk).2, GlobalTheory.T.exists_closedDisc_extension_breuilKisinHom l K bk,
    (GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk).2.2.1⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphism
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per Matrix

namespace GlobalTheory.BKReal.Full

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

section Lat

variable {G : Type} [Group G] [TopologicalSpace G] {T T' : LocLat G ℚ_[l] K O}


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem latW_smul (f : LatHom T.L T'.L) (r : OW l O) (y : TW (OW l O) T) :
    latW f (r • y) = r • latW f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem latW_frob (f : LatHom T.L T'.L) (y : TW (OW l O) T) :
    latW f (TWmap (frobOW l O) T y) = TWmap (frobOW l O) T' (latW f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

def latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ↥T.L.T →ₗ[ℤ_[l]] ↥T'.L.T :=
  letI := zlLat T
  letI := zlLat T'
  { toFun := (f.f.restrictScalars O).restrict f.T_le
    map_add' := map_add _
    map_smul' := fun z x => ((f.f.restrictScalars O).restrict f.T_le).map_smul (algebraMap ℤ_[l] O z) x }


omit [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in
theorem kappa_latZ (f : LatHom T.L T'.L) :
    letI := zlLat T
    letI := zlLat T'
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T' ((latZ f).lTensor (WCb l) y) = latW f (kappa T y) := by
  let _ := zlLat T
  let _ := zlLat T'
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ}

theorem exists_isMapOf (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (f : LatHom T.L T'.L)
    (h : ∀ (m : Vec K a ι) (hm : m ∈ P.M), ∃ (m' : Vec K a κ) (hm' : m' ∈ Q.M),
      latW f (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) = I'.j (toW t ϖ Q ⟨m', mem_ME_of_mem_M hm'⟩)) :
    ∃ F, IsMapOf I I' f F := by
  have hb : ∀ j : ι, (fun _ => Pi.single j 1 : Vec K a ι) ∈ P.M := fun j => mem_tot.2 fun τ i => by
    by_cases hij : i = j
    · subst hij; rw [Pi.single_eq_same]; exact one_mem _
    · rw [Pi.single_eq_of_ne hij]; exact zero_mem _
  have hb' : ∀ j : ι, toW t ϖ P ⟨_, mem_ME_of_mem_M (hb j)⟩ = Pi.single j 1 := fun j => funext fun i => by
    rw [toW_apply]
    by_cases hij : i = j
    · subst hij
      rw [Pi.single_eq_same (M := fun _ => OW l O), ← map_one (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_same (M := fun _ => K⟦X⟧) i 1))
    · rw [Pi.single_eq_of_ne (M := fun _ => OW l O) hij, ← map_zero (ϖ.iW t K)]
      exact congrArg _ (funext fun τ => Subtype.ext (Pi.single_eq_of_ne (M := fun _ => K⟦X⟧) hij 1))
  choose m hm hmj using fun j => h _ (hb j)
  simp only [hb'] at hmj
  let Y : Matrix κ ι (OW l O) :=
    Matrix.of fun i j => inclO l O (ϖ.iTot t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩)
  have hY : ∀ j, toW t ϖ Q ⟨m j, mem_ME_of_mem_M (hm j)⟩ = fun i => Y i j := fun j => funext fun i =>
    ϖ.iW_of_mem t K fun τ => ⟨m j τ i, mem_tot.1 (hm j) τ i⟩
  have key : ∀ v, I'.j (Y *ᵥ v) = latW f (I.j v) := fun v => by
    have h1 : Y *ᵥ v = ∑ j, v j • fun i => Y i j := by
      ext1 i
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [pi_eq_sum_univ' v, map_sum, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul I.j, latW_smul, hmj, hY, map_smul I'.j]
  have hmat : Y * frobMat t ϖ P = frobMat t ϖ Q * Y.map (frobOW l O) := by
    have h1 : ∀ v, Y *ᵥ phiW t ϖ P v = phiW t ϖ Q (Y *ᵥ v) := fun v => I'.j.injective (by
      rw [key, I.j_φ, latW_frob, I'.j_φ, key])
    ext1 i j
    have h2 := congrFun (h1 (Pi.single j 1)) i
    have h3 : (fun k => frobOW l O (Pi.single (M := fun _ : ι => OW l O) j 1 k)) = Pi.single j 1 :=
      funext fun k => by simp only [Pi.single_apply, apply_ite (frobOW l O), map_one, map_zero]
    rw [phiW_apply, phiW_apply, h3, Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
      Matrix.mulVec_single_one] at h2
    exact h2
  refine ⟨⟨fun τ => Matrix.of fun i j => m j τ i, fun τ i j => mem_tot.1 (hm j) τ i, fun τ => ?_⟩, key⟩
  ext1 i j
  have h1 := congrFun₂ hmat i j
  change ∑ k, inclO l O (ϖ.iTot t K _) * ϖ.iW t K _ =
    ∑ k, ϖ.iW t K _ * frobOW l O (inclO l O (ϖ.iTot t K _)) at h1
  simp only [frobOW_inclO, ← PiSys.iTot_frob] at h1
  simp only [← ϖ.iW_of_mem t K, ← map_mul] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_sum] at h1
  have h2 := congrArg Subtype.val (congrFun (ϖ.iW_injective t K h1) τ)
  rw [Finset.sum_apply, Finset.sum_apply, AddSubmonoidClass.coe_finsetSum,
    AddSubmonoidClass.coe_finsetSum] at h2
  exact h2

end Lat

theorem main (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a]
    [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ)
    (I : Ident t ϖ P T) (I' : Ident t ϖ Q T') (H : IsBK I) (H' : IsBK I') (f : LatHom T.L T'.L) :
    ∃ F, IsMapOf I I' f F := by
  let _ := zlLat T
  let _ := zlLat T'
  obtain ⟨E, j, hE, h⟩ := H
  obtain ⟨E', j', hE', h'⟩ := H'
  obtain ⟨u, hu, -⟩ := (BS l (ϖ.field a) _ _ (isAinf_ainfObj _)).2 _ _ _ _ E E' j j' hE hE' (latZ f)
    fun g x => Subtype.ext (f.equiv g x)
  refine exists_isMapOf I I' f fun m hm => (h' _).1 ?_
  obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
  refine ⟨u.u _ x, ?_⟩
  rw [hx, ← u.u_tr, hu]
  exact (kappa_latZ f _).symm

end GlobalTheory.BKReal.Full
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFullFaithfulnessLatticeMorphismStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_full_faithfulness_lattice_morphism : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (T T' : Lat a O K ϖ) (I : Ident t ϖ P T) (I' : Ident t ϖ Q T'), IsBK I → IsBK I' → ∀ f : LatHom T.L T'.L, ∃ F, IsMapOf I I' f F := by
  first | exact @GlobalTheory.BKReal.Full.main | exact GlobalTheory.BKReal.Full.main | (intros; apply GlobalTheory.BKReal.Full.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameFixedLift
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

namespace GlobalTheory.TameFixedLift

open Pointwise

theorem transfer {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [Algebra ℚ Ω]
    (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hfix : ∀ x : E, σ (algebraMap E Ω x) = algebraMap E Ω x) :
    ∃ g ∈ Ine (F := E) A, cycZ (F := E) (Ω := Ω) l g = cycZ (F := ℚ) (Ω := Ω) l σ := by
  refine ⟨AlgEquiv.ofRingEquiv (f := (σ : Ω ≃+* Ω)) hfix, ⟨?_, hσ.2⟩, rfl⟩
  have h : σ • A = A := hσ.1
  exact h

theorem root_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (σ : G ℚ Ω) (u : ℤ_[l])
    (h : ((cycZ (F := ℚ) (Ω := Ω) l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u)
    (t : Ω) (ht : t ^ l ^ n = 1) : σ t = t := by
  have : CharZero Ω := algebraRat.charZero Ω
  have : ∀ i : ℕ, NeZero ((l ^ i : ℕ) : Ω) := fun i =>
    ⟨by exact_mod_cast pow_ne_zero i (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec l (n := n) (σ : Ω ≃+* Ω) t ht
  have h2 : ((cyclotomicCharacter Ω l (σ : Ω ≃+* Ω) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) ^ n * u := h
  have h3 : PadicInt.toZModPow n ((l : ℤ_[l]) ^ n) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZModPow]; exact Ideal.mem_span_singleton_self _
  rw [h2, map_add (f := _), map_mul, h3, zero_mul, add_zero, map_one] at h1
  have h4 : t ^ (1 : ZMod (l ^ n)).val = t := by
    rw [ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 ht, pow_one]
  rw [h4] at h1
  exact h1

theorem exists_place (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    ∃ w, w ∈ placesOver E l := by
  have hl : l.Prime := Fact.out
  have hnu : Ideal.span {(l : 𝓞 E)} ≠ ⊤ := by
    intro h
    have h1 := congrArg Ideal.absNorm h
    rw [Ideal.absNorm_span_natCast, Ideal.absNorm_top] at h1
    rcases Nat.pow_eq_one.mp h1 with h2 | h2
    · exact hl.one_lt.ne' h2
    · exact Module.finrank_pos.ne' h2
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hmem : (l : 𝓞 E) ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  rintro rfl
  rw [Ideal.mem_bot] at hmem
  exact hl.ne_zero (by exact_mod_cast hmem)

private theorem eq_one_of_cong {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hc : Nat.Coprime m l) {z : Ω} (hz : z ^ m = 1)
    (h1 : A.valuation (z - 1) < 1) : z = 1 := by
  by_contra hne
  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have hz1 : A.valuation z ≤ 1 := by
    have := Valuation.map_add_le A.valuation h1.le (le_of_eq (map_one A.valuation))
    simpa using this
  have hp : ∀ i : ℕ, A.valuation (z ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show z ^ (i + 1) - 1 = (z ^ i - 1) * z + (z - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h1
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hz1) ih
  have hs : ∑ i ∈ Finset.range m, z ^ i = 0 := by
    have := mul_geom_sum z m
    rw [hz, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have hm : A.valuation (m : Ω) < 1 := by
    have h2 : A.valuation (∑ i ∈ Finset.range m, (z ^ i - 1)) < 1 :=
      Valuation.map_sum_lt _ one_ne_zero fun i _ => hp i
    rw [Finset.sum_sub_distrib, hs] at h2
    simpa using h2
  have hb : (1 : Ω) = (m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω) := by
    have h3 := Nat.gcd_eq_gcd_ab m l
    rw [hc.gcd_eq_one] at h3
    exact_mod_cast congrArg (Int.cast : ℤ → Ω) h3
  have h4 : A.valuation ((m : Ω) * ((Nat.gcdA m l : ℤ) : Ω) + (l : Ω) * ((Nat.gcdB m l : ℤ) : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_ <;> rw [map_mul]
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hm
    · exact lt_of_le_of_lt (mul_le_of_le_one_right' (hint _)) hA
  rw [← hb, map_one] at h4
  exact lt_irrefl _ h4

private theorem tame_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) {l m : ℕ}
    (hA : A.valuation (l : Ω) < 1) (hm : m ≠ 0) (hc : Nat.Coprime m l) (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (z : Ω) (hz : z ^ m = 1) : σ z = z := by
  have hv : A.valuation z = 1 := by
    have := congrArg A.valuation hz
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hm).mp this
  have hz0 : z ≠ 0 := by rintro rfl; simp at hv
  have h3 : A.valuation (σ z - z) < 1 := hσ.2 z hv.le
  have h4 : σ z / z = 1 := eq_one_of_cong A hA hc
    (by rw [div_pow, ← map_pow, hz, map_one, div_one]) (by
      rw [show σ z / z - 1 = (σ z - z) / z by field_simp, map_div₀, hv, div_one]
      exact h3)
  exact (div_eq_one_iff_eq hz0).mp h4

private theorem loc_fix {R : Ranks} (H : Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω] [Algebra ℚ Ω]
    [IsAlgClosed Ω] (A : ValuationSubring Ω) {l : ℕ} (hl : l.Prime) (hA : A.valuation (l : Ω) < 1)
    (σ : G ℚ Ω) (hσ : σ ∈ Ine (F := ℚ) A)
    (hroot : ∀ t : Ω, t ^ l ^ H.condN.factorization l = 1 → σ t = t) (x : H.E) :
    σ (algebraMap H.E Ω x) = algebraMap H.E Ω x := by
  have hN : H.condN ≠ 0 := H.condN_ne_zero
  refine H.image_mem_of_roots (algebraMap H.E Ω) (RingHom.eqLocusField (σ : Ω →+* Ω) (RingHom.id Ω))
    (fun y hy => ?_) x
  show σ y = y
  have hy0 : y ≠ 0 := by rintro rfl; simp [hN] at hy
  have hmul := Nat.ordProj_mul_ordCompl_eq_self H.condN l
  have hco : Nat.Coprime l (ordCompl[l] H.condN) := Nat.coprime_ordCompl hl hN
  have h1 := hroot (y ^ ordCompl[l] H.condN) (by rw [← pow_mul, mul_comm, hmul, hy])
  have h2 := tame_fix A hA (Nat.ordCompl_pos l hN).ne' hco.symm σ hσ (y ^ ordProj[l] H.condN)
    (by rw [← pow_mul, hmul, hy])
  rw [map_pow] at h1 h2
  have h3 : (σ y / y) ^ Nat.gcd (ordProj[l] H.condN) (ordCompl[l] H.condN) = 1 :=
    pow_gcd_eq_one.2 ⟨by rw [div_pow, h2, div_self (pow_ne_zero _ hy0)],
      by rw [div_pow, h1, div_self (pow_ne_zero _ hy0)]⟩
  rw [(Nat.Coprime.pow_left _ hco).gcd_eq_one, pow_one] at h3
  exact (div_eq_one_iff_eq hy0).mp h3

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) , ∃ w ∈ placesOver H.E (N.l i), ∀ u : ℤ_[N.l i], ∃ g ∈ Ine (F := H.E) (N.plOm.1 w), ((cycZ (F := H.E) (Ω := N.Om) (N.l i) g : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) = 1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by
  intro R H what₂ N i
  obtain ⟨w, hw⟩ := exists_place H.E (N.l i)
  refine ⟨w, hw, fun u => ?_⟩
  have : CharZero N.Om := charZero_of_injective_algebraMap (algebraMap H.E N.Om).injective
  have : IsAlgClosed N.Om := IsAlgClosure.isAlgClosed H.E
  have : IsScalarTower ℚ H.E N.Om := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  have : IsAlgClosure ℚ N.Om := IsAlgClosure.ofAlgebraic ℚ H.E N.Om
  have hA : (N.plOm.1 w).valuation (N.l i : N.Om) < 1 := by
    have := (N.plOm.2 w (N.l i : 𝓞 H.E)).2 hw
    simpa using this
  have hs : 1 ≤ N.s0 i := UpperTheory.KStar.S0.one_le_localLevel N i
  have hunit : IsUnit (1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u) := by
    have hm : -((N.l i : ℤ_[N.l i]) ^ N.s0 i * u) ∈ IsLocalRing.maximalIdeal ℤ_[N.l i] := by
      rw [PadicInt.maximalIdeal_eq_span_p, neg_mem_iff, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (dvd_pow_self _ (by omega)) _
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hm
    simpa using this
  obtain ⟨σ, hσ, hv⟩ := GlobalTheory.T.cyclotomicChar_inertia_surjective N.Om (N.l i) (N.plOm.1 w) hA hunit.unit
  have hv' : ((cycZ (F := ℚ) (Ω := N.Om) (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) =
      1 + (N.l i : ℤ_[N.l i]) ^ N.s0 i * u := by rw [hv]; rfl
  obtain ⟨k, hk⟩ := pow_dvd_pow (N.l i) (UpperTheory.KStar.S0.factorization_conductor_le_localLevel N i)
  obtain ⟨g, hg, hc⟩ := transfer (E := H.E) (N.plOm.1 w) (N.l i) σ hσ
    (loc_fix H _ (N.lPrime i).out hA σ hσ fun t ht =>
      root_fix (N.l i) (N.s0 i) σ u hv' t (by rw [hk, pow_mul, ht, one_pow]))
  exact ⟨g, hg, by rw [hc, hv']⟩

end GlobalTheory.TameFixedLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicative
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.GaussMul

open Filter

theorem norm_sum_lt_of_ultra {E ι : Type} [SeminormedAddCommGroup E] [IsUltrametricDist E] (s : Finset ι)
    (f : ι → E) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) : ‖∑ i ∈ s, f i‖ < C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt
      (max_lt (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem exists_eq_sup {f : ℕ → ℝ} {M : ℝ} (hM : 0 < M) (hle : ∀ n, f n ≤ M)
    (hsup : ∀ r : ℝ, 0 ≤ r → (∀ n, f n ≤ r) → M ≤ r) (ht : Tendsto f atTop (nhds 0)) : ∃ n, f n = M := by
  by_contra hne
  push_neg at hne
  have hlt : ∀ n, f n < M := fun n => lt_of_le_of_ne (hle n) (hne n)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hM)))
  obtain ⟨k, -, hk⟩ := Finset.exists_max_image (Finset.range (N + 1)) f ⟨0, by simp⟩
  have h1 : M ≤ max (M / 2) (f k) := hsup _ ((half_pos hM).le.trans (le_max_left _ _)) fun n => by
    by_cases hn : n < N + 1
    · exact (hk n (Finset.mem_range.2 hn)).trans (le_max_right _ _)
    · exact (hN n (by omega)).le.trans (le_max_left _ _)
  exact absurd h1 (not_le.2 (max_lt (half_lt_self hM) (hlt k)))

theorem gauss {D : Type} [NormedRing D] [IsUltrametricDist D] (hm : ∀ x y : D, ‖x * y‖ = ‖x‖ * ‖y‖) {ρ : ℝ}
    (hρ : 0 < ρ) (p q : ℕ → D) {P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q) (hp : ∀ n, ‖p n‖ * ρ ^ n ≤ P)
    (hq : ∀ n, ‖q n‖ * ρ ^ n ≤ Q) (hp0 : ∃ n, ‖p n‖ * ρ ^ n = P) (hq0 : ∃ n, ‖q n‖ * ρ ^ n = Q) :
    ∃ N, ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, p x.1 * q x.2‖ * ρ ^ N = P * Q := by
  classical
  set n₀ := Nat.find hp0
  set m₀ := Nat.find hq0
  have hn₀ : ‖p n₀‖ * ρ ^ n₀ = P := Nat.find_spec hp0
  have hm₀ : ‖q m₀‖ * ρ ^ m₀ = Q := Nat.find_spec hq0
  refine ⟨n₀ + m₀, ?_⟩
  have hρN : 0 < ρ ^ (n₀ + m₀) := pow_pos hρ _
  have hmem : (n₀, m₀) ∈ Finset.HasAntidiagonal.antidiagonal (n₀ + m₀) := by simp
  rw [← Finset.add_sum_erase _ _ hmem]
  have hdom : ‖p n₀ * q m₀‖ * ρ ^ (n₀ + m₀) = P * Q := by
    rw [hm, pow_add, ← hn₀, ← hm₀]; ring
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (n₀ + m₀)).erase (n₀, m₀), p x.1 * q x.2‖ < P * Q / ρ ^ (n₀ + m₀) := by
    refine norm_sum_lt_of_ultra _ _ (div_pos (mul_pos hP hQ) hρN) fun x hx => ?_
    rw [lt_div_iff₀ hρN]
    obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have e : ‖p x.1 * q x.2‖ * ρ ^ (n₀ + m₀) = (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) := by
      rw [hm, ← hx, pow_add]; ring
    rw [e]
    have h1 : 0 ≤ ‖p x.1‖ * ρ ^ x.1 := by positivity
    have h2 : 0 ≤ ‖q x.2‖ * ρ ^ x.2 := by positivity
    by_cases h : x.1 < n₀
    · have hlt : ‖p x.1‖ * ρ ^ x.1 < P := lt_of_le_of_ne (hp _) (Nat.find_min hp0 h)
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ (‖p x.1‖ * ρ ^ x.1) * Q :=
            mul_le_mul_of_nonneg_left (hq _) h1
        _ < P * Q := mul_lt_mul_of_pos_right hlt hQ
    · have h' : x.2 < m₀ := by
        by_contra h''
        apply hne
        ext <;> simp <;> omega
      have hlt : ‖q x.2‖ * ρ ^ x.2 < Q := lt_of_le_of_ne (hq _) (Nat.find_min hq0 h')
      calc (‖p x.1‖ * ρ ^ x.1) * (‖q x.2‖ * ρ ^ x.2) ≤ P * (‖q x.2‖ * ρ ^ x.2) :=
            mul_le_mul_of_nonneg_right (hp _) h2
        _ < P * Q := mul_lt_mul_of_pos_left hlt hP
  have hdom' : ‖p n₀ * q m₀‖ = P * Q / ρ ^ (n₀ + m₀) := by
    rw [eq_div_iff hρN.ne', hdom]
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdom']; exact hrest.ne'), hdom',
    max_eq_left hrest.le, div_mul_cancel₀ _ hρN.ne']

end GlobalTheory.BSP.GaussMul

namespace GlobalTheory.BSP.GaussMul

theorem norm_mul_disc (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0) (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (x y : bk.DS ρ) : ‖x * y‖ = ‖x‖ * ‖y‖ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk ρ hρ0 hρ1
  haveI : IsUltrametricDist (Disc l (0 : Wq l bk.a) 1) := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l (Wq l bk.a) 0 1).1
  have hm0 := (GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk).1
  have hρ : (0 : ℝ) < ρ := NNReal.coe_pos.2 hρ0

  have step1 : ∀ s t : bk.S, ‖toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t‖ =
      ‖toDisc l (X : bk.S) ρ s‖ * ‖toDisc l (X : bk.S) ρ t‖ := by
    intro s t
    rcases eq_or_ne (toDisc l (X : bk.S) ρ s) 0 with hu | hu
    · simp [hu]
    rcases eq_or_ne (toDisc l (X : bk.S) ρ t) 0 with hv | hv
    · simp [hv]
    have hP : 0 < ‖toDisc l (X : bk.S) ρ s‖ := norm_pos_iff.2 hu
    have hQ : 0 < ‖toDisc l (X : bk.S) ρ t‖ := norm_pos_iff.2 hv
    obtain ⟨N, hN⟩ := gauss hm0 hρ (fun n => a n (toDisc l (X : bk.S) ρ s)) (fun n => a n (toDisc l (X : bk.S) ρ t))
      hP hQ (fun n => ha2 n _) (fun n => ha2 n _)
      (exists_eq_sup hP (fun n => ha2 n _) (ha3 _) (ha4 _)) (exists_eq_sup hQ (fun n => ha2 n _) (ha3 _) (ha4 _))
    have hconv : a N (toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t) =
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal N, a x.1 (toDisc l (X : bk.S) ρ s) * a x.2 (toDisc l (X : bk.S) ρ t) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_mul, ha1, coeff_mul, map_sum]
      exact Finset.sum_congr rfl fun x _ => by rw [map_mul, ha1, ha1]
    refine le_antisymm (norm_mul_le _ _) ?_
    rw [← hN, ← hconv]
    exact ha2 N _

  have hlm := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l bk.S (X : bk.S) ρ).2.1
  have hl0 : (0 : ℝ) < (l : ℝ) := Nat.cast_pos.2 hl.out.pos
  have hlpow : ∀ (n : ℕ) (z : bk.DS ρ), ‖z * ((l : ℕ) : bk.DS ρ) ^ n‖ = ‖z‖ / (l : ℝ) ^ n := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, ← mul_assoc, mul_comm _ ((l : ℕ) : bk.DS ρ), hlm, ih, pow_succ, div_div]
  have hpre : ∀ p : PreDisc l (X : bk.S) ρ, ∃ (n : ℕ) (s : bk.S),
      ofPre l (X : bk.S) ρ p * ((l : ℕ) : bk.DS ρ) ^ n = toDisc l (X : bk.S) ρ s := by
    intro p
    obtain ⟨n, s, h⟩ := IsLocalization.Away.surj ((l : ℕ) : bk.S) p
    refine ⟨n, s, ?_⟩
    have h' := congrArg (ofPre l (X : bk.S) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at h'
    exact h'
  have step2 : ∀ p q : PreDisc l (X : bk.S) ρ, ‖ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q‖ =
      ‖ofPre l (X : bk.S) ρ p‖ * ‖ofPre l (X : bk.S) ρ q‖ := by
    intro p q
    obtain ⟨n, s, hs⟩ := hpre p
    obtain ⟨m, t, ht⟩ := hpre q
    have e : ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q * ((l : ℕ) : bk.DS ρ) ^ (n + m) =
        toDisc l (X : bk.S) ρ s * toDisc l (X : bk.S) ρ t := by
      rw [← hs, ← ht, pow_add]; ring
    have h1 := hlpow (n + m) (ofPre l (X : bk.S) ρ p * ofPre l (X : bk.S) ρ q)
    rw [e, step1, ← hs, ← ht, hlpow, hlpow, pow_add, div_mul_div_comm] at h1
    exact ((div_left_inj' (by positivity)).1 h1).symm
  exact (denseRange_ofPre l (X : bk.S) ρ).induction_on₂ (p := fun x y : bk.DS ρ => ‖x * y‖ = ‖x‖ * ‖y‖)
    (isClosed_eq (continuous_norm.comp (continuous_fst.mul continuous_snd))
      ((continuous_norm.comp continuous_fst).mul (continuous_norm.comp continuous_snd))) step2 x y

theorem norm_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ :=
  fun l _ K bk ρ h0 h1 x y => norm_mul_disc l K bk ρ h0 h1 x y

end GlobalTheory.BSP.GaussMul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinClosedDiscNormMulMultiplicativeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_closedDisc_norm_mul_multiplicative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ x y : bk.DS ρ, ‖x * y‖ = ‖x‖ * ‖y‖ := by
  first | exact @GlobalTheory.BSP.GaussMul.norm_mul | exact GlobalTheory.BSP.GaussMul.norm_mul | (intros; apply GlobalTheory.BSP.GaussMul.norm_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffProdOneSubCMulX
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem coeff_prod_one_sub_C_mul_X (c : ℂ) (α : Multiset ℂ) (k : ℕ) :
    ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C (c * a) * Polynomial.X).prod).coeff k
      = (-1 : ℂ) ^ k * c ^ k * α.esymm k := by
  induction α using Multiset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [Multiset.esymm]
    | succ k => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, sub_mul, one_mul, mul_assoc, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul]
    cases k with
    | zero => rw [ih]; simp [Multiset.esymm]
    | succ k =>
      have h : (a ::ₘ s).esymm (k + 1) = s.esymm (k + 1) + a * s.esymm k := by
        simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]
      rw [Polynomial.coeff_X_mul, ih, ih, h]
      ring

theorem normalised_esymm_eq_coeff :
    ∀ (r : ℕ) (q : ℝ), 0 < q → ∀ (α : Multiset ℂ), Multiset.card α = r → ∀ k, k ≤ r → (-1 : ℂ) ^ k * (q : ℂ) ^ (k * (k - 1) / 2) * ((q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2) * α.esymm k) = ((α.map fun a => (1 : Polynomial ℂ) - Polynomial.C ((q : ℂ) ^ (((r : ℂ) - 1) / 2) * a) * Polynomial.X).prod).coeff k := by
  intro r q hq α _ k _
  rw [coeff_prod_one_sub_C_mul_X]
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hk : ((k * (k - 1) / 2 : ℕ) : ℂ) = (k : ℂ) * ((k : ℂ) - 1) / 2 := by
    rw [← Nat.choose_two_right, Nat.cast_choose_two]
  have h : (q : ℂ) ^ (k * (k - 1) / 2) * (q : ℂ) ^ (((k : ℂ) * ((r : ℂ) - k)) / 2)
      = ((q : ℂ) ^ (((r : ℂ) - 1) / 2)) ^ k := by
    rw [← Complex.cpow_natCast (q : ℂ) (k * (k - 1) / 2), ← Complex.cpow_add _ _ hq0, hk,
      ← Complex.cpow_nat_mul]
    congr 1
    ring
  rw [← h]
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDense
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CharDualDense

theorem t2_O0 {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    T2Space (X.O0 i) :=
  (IsAdic.isHausdorff_iff (X.twistBaseCoefficientRing_isAdic i)).1 inferInstance

theorem finite_S0_conj {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) :
    ((X.S0 i : Set (PlE D.host)) ∪ {P | ∃ P' ∈ X.S0 i, IsConjPl D.host P P'}).Finite := by
  refine (X.S0 i).finite_toSet.union ?_
  refine ((X.S0 i).finite_toSet.biUnion (t := fun P' => {P | IsConjPl D.host P' P}) fun P' _ => ?_).subset ?_
  · exact (show ({P | IsConjPl D.host P' P} : Set (PlE D.host)).Subsingleton from
      fun a ha b hb => GlobalTheory.TwistDet.isConjPl_unique ha hb).finite
  · rintro P ⟨P', hP', hc⟩
    exact Set.mem_biUnion (x := P') hP' (GlobalTheory.TwistDet.isConjPl_symm hc)

theorem charDual_of_frobDual : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i),
    FrobDual i s → CharDual i s := by
  intro D hF i s hFD g g' hg'
  haveI := t2_O0 D.ntw i
  have e : g' = GlobalTheory.TwistDet.cConj D.ntw g := by
    ext x
    rw [hg', GlobalTheory.TwistDet.cConj_apply]
  subst e
  refine GlobalTheory.TypeLeaf.charpoly_eq_of_dense (Gen.GE D.nd) (D.ntw.O0 i) D.R.r
    (fun g => Tdual i s (GlobalTheory.TwistDet.cConj D.ntw g))
    (fun g => ((((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s g)) _
    (hF _ (finite_S0_conj D.ntw i))
    ((GlobalTheory.PrimeToInertia.continuous_Tdual i s).comp (GlobalTheory.ResConjTriv.continuous_cConj D.ntw)) ?_ ?_ g
  · have h1 : Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
      (GlobalTheory.PrimeToInertia.continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (GlobalTheory.PrimeToInertia.l_mem i)).comp
        (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))
    exact (h1.pow _).smul (GlobalTheory.PrimeToInertia.continuous_Tmat i s)
  · rintro σ ⟨w, hwT, hsp, B, hB, hσ⟩
    refine hFD w (fun h => hwT (Or.inl h)) hsp (fun P' hc h => hwT (Or.inr ⟨P', h, hc⟩)) B hB σ _ hσ
      (GlobalTheory.TwistDet.cConj_apply D.ntw σ)

end GlobalTheory.CharDualDense

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjDualCharpolyOfSplitFrobeniusDenseStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjDualCharpoly_of_splitFrobenius_dense : ∀ (D : D7), GlobalTheory.TypeLeaf.FrobDense D → ∀ (i : D.ntw.Tw) (s : D.ntw.Sig i), FrobDual i s → CharDual i s := by
  first | exact @GlobalTheory.CharDualDense.charDual_of_frobDual | exact GlobalTheory.CharDualDense.charDual_of_frobDual | (intros; apply GlobalTheory.CharDualDense.charDual_of_frobDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultiset
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NoJumpMult

open Module TensorProduct

section Gen
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : Formalism.WeaklyAdmissibleFiltrations.PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FilV PD (LL := LL) (V := V) a := by
  have h := PD.Fil_anti a
  unfold Formalism.WeaklyAdmissibleFiltrations.FilV
  have : AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil (a + 1)).restrictScalars Qp).subtype =
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype).comp
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
          (Submodule.inclusion (show (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp from h))) := by
    ext x y; rfl
  rw [this]
  exact LinearMap.range_comp_le_range _ _

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) ≤ Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a ≤ Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero (τ : K →ₐ[Qp] LL) (a : ℤ) (hpos : 0 < finrank LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ))
    (hj : Formalism.WeaklyAdmissibleFiltrations.IsJumpV PD ρ τ a) : Formalism.WeaklyAdmissibleFiltrations.multV PD ρ τ a ≠ 0 := by
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have : FiniteDimensional LL ↥(Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)
  have hlt : Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ (a + 1) < Formalism.WeaklyAdmissibleFiltrations.FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) hj
  have := Submodule.finrank_lt_finrank_of_lt hlt
  unfold Formalism.WeaklyAdmissibleFiltrations.multV
  omega
end Gen

end GlobalTheory.NoJumpMult

namespace GlobalTheory.NoJumpMult

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h1 := D.R.two_le_m; have h2 := D.R.m_add_three_le_k
  unfold Formalism.BasicNotions.Ranks.r; omega

theorem noJump_of_jumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro D bkP i s ι J hH hJ hG v hv τ a ha
    obtain ⟨τc, hτc, -⟩ := GlobalTheory.ReadEmbEx.exists_readEmb D bkP i ι v hv τ
    have hdR := (hH v hv (Tgl i s) (Set.mem_insert_of_mem _ rfl)).1
    have hK : 0 < Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 := by
      have := (bkP.br i v hv).Kw.2
      exact Module.finrank_pos
    have hpos : 0 < Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) := by
      have : Module.finrank ↥(bkP.br i v hv).LL.1
        ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s))) =
          Module.finrank ℚ_[D.ntw.l i] ↥(bkP.br i v hv).Kw.1 * D.R.r := hdR
      rw [this]; exact Nat.mul_pos hK (r_pos D)
    have hm := multV_ne_zero _ _ τ a hpos ha
    rw [hJ v hv τ τc hτc a] at hm
    have hmem : a ∈ J τc := by
      by_contra hn
      exact hm (by simp [Multiset.count_eq_zero.mpr hn])
    exact (hG τc).2.2 a hmem

end GlobalTheory.NoJumpMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoHodgeJumpOfGoodJumpMultisetStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noHodgeJump_of_goodJumpMultiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NoJump bkP i s := by
  first | exact @GlobalTheory.NoJumpMult.noJump_of_jumps | exact GlobalTheory.NoJumpMult.noJump_of_jumps | (intros; apply GlobalTheory.NoJumpMult.noJump_of_jumps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSelmerCocycleMapAlgHom
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSelmerCocycleMapAlgHom
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime

theorem univ_map : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  intro D N X bkP i s B _ _ A _ _ π κ κ' hκ Q a Φ Z hU Y _ _ _ _
  letI : Module B Y := Module.compHom Y π.toRingHom
  have hsm : ∀ (b : B) (y : Y), b • y = π b • y := fun _ _ => rfl
  obtain ⟨hrep, hsel⟩ := GlobalTheory.T.selmerCocycles_scalarChange_transfer D N X bkP i s B A π κ κ' hκ Y hsm
  obtain ⟨h1, h2, h3⟩ := hU Y
  have hm : ∀ x : Fin a → Y, matAct (Φ.map π) x = matAct Φ x := fun _ => rfl
  have hr : ∀ g (x : Fin a → Y), rect ((Z g).map π) x = rect (Z g) x := fun _ _ => rfl
  have hc : ∀ f, Cob (repOn (Tgl i s) κ Y) f ↔ Cob (repOn (Tgl i s) κ' Y) f := fun f => by
    simp only [Cob, hrep]
  simp only [hm, hr]
  refine ⟨fun x hx => (hsel _ _).1 (h1 x hx), fun x hx hb => h2 x hx ((hc _).2 hb), fun f hf => ?_⟩
  obtain ⟨x, hx, hb⟩ := h3 f ((hsel _ _).2 hf)
  exact ⟨x, hx, (hc _).1 hb⟩

end GlobalTheory.NewPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalSelmerCocycleMapAlgHomStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.universalSelmerCocycle_map_algHom : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), ∀ (B : Type) [CommRing B] [Algebra (X.O0 i) B] (A : Type) [CommRing A] [Algebra (X.O0 i) A] (π : B →ₐ[X.O0 i] A) (κ : GE N →* Bˣ) (κ' : GE N →* Aˣ), (∀ g, ((κ' g : Aˣ) : A) = π (κ g : Bˣ)) → ∀ (Q : Finset (PlE D.host)) (a : ℕ) (Φ : Matrix (Fin a) (Fin a) B) Z, Univ bkP i s κ Q Φ Z → Univ bkP i s κ' Q (Φ.map π) (fun g => (Z g).map π) := by
  first | exact @GlobalTheory.NewPrime.univ_map | exact GlobalTheory.NewPrime.univ_map | (intros; apply GlobalTheory.NewPrime.univ_map <;> assumption)
end
end
