module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreserving
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLattice
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

theorem exists_lat_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A)
    (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  intro E _ _ _ w K e a B b L hL
  obtain ⟨hfg, hspan⟩ := hL
  haveI : Module.Finite K.O L := Module.Finite.iff_fg.mpr hfg
  haveI : NoZeroSMulDivisors K.O B.A := ⟨fun {r x} h => by
    rw [← algebraMap_smul K.E r x] at h
    rcases smul_eq_zero.mp h with h | h
    · left; exact (IsFractionRing.injective K.O K.E) (by simpa using h)
    · right; exact h⟩
  haveI : Module.Free K.O L := Module.free_of_finite_type_torsion_free'
  let y := Module.Free.chooseBasis K.O L
  let v : Module.Free.ChooseBasisIndex K.O L → B.A := fun i => (y i : B.A)
  have hli : LinearIndependent K.O v := y.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hliE : LinearIndependent K.E v := (LinearIndependent.iff_fractionRing K.O K.E).mp hli
  have hLv : Submodule.span K.O (Set.range v) = L := by
    have : Set.range v = L.subtype '' Set.range y := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, y.span_eq, Submodule.map_subtype_top]
  have hspE : Submodule.span K.E (Set.range v) = ⊤ := by
    rw [← Submodule.span_span_of_tower K.O K.E, hLv]; exact hspan
  let c := Module.Basis.mk hliE hspE.ge
  let c' := c.reindex (c.indexEquiv b)
  let U : (Matrix (Fin a) (Fin a) K.E)ˣ :=
    ⟨b.toMatrix c', c'.toMatrix b, b.toMatrix_mul_toMatrix_flip c', c'.toMatrix_mul_toMatrix_flip b⟩
  refine ⟨Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U, ?_⟩
  rw [latOf_eq, ← hLv]
  have hcol : ∀ j, (ofCrd e b fun i =>
      (Units.map (e.toRingHom.mapMatrix : Matrix (Fin a) (Fin a) K.E →+* _).toMonoidHom U).val i j) = c' j := by
    intro j
    rw [← ofCrd_crd e b (c' j)]
    congr 1
  simp only [hcol]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨(c.indexEquiv b).symm j, ?_⟩
    simp [c', c, v]
  · rintro ⟨i, rfl⟩
    refine ⟨c.indexEquiv b i, ?_⟩
    simp [c', c, v]

end GlobalTheory.TwOrbLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLLatticeSpannedByGLColumnsEqFullLatticeStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (b : Module.Basis (Fin a) K.E B.A) (L : Submodule K.O B.A), GlobalTheory.UnitLemma.IsLat K.O K.E L → ∃ q : GLw a w, GlobalTheory.TwLat.lat e b q = L := by
  first | exact @GlobalTheory.TwOrbLat.exists_lat_eq | exact GlobalTheory.TwOrbLat.exists_lat_eq | (intros; apply GlobalTheory.TwOrbLat.exists_lat_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.NonarchShell

theorem exists_compact_shell_nsmul : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (V : Set (Fin N → v.adicCompletion F)), V ∈ nhds 0 →
      ∃ K : Set (Fin N → v.adicCompletion F), IsCompact K ∧ (0 : Fin N → v.adicCompletion F) ∉ K ∧
        ∀ t, t ∉ V → ∃ n : ℕ, n • t ∈ K := by
  intro F _ _ v N V hV
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  set q : ℕ := Ideal.absNorm v.asIdeal with hqdef
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : ‖(q : v.adicCompletion F)‖ < 1 := by
    have := (NumberField.FinitePlace.norm_lt_one_iff_mem F v ((q : 𝓞 F))).2 (Ideal.absNorm_mem _)
    rwa [map_natCast, map_natCast] at this
  have hqne : (q : v.adicCompletion F) ≠ 0 := by
    rw [← map_natCast (algebraMap F (v.adicCompletion F)) q]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hq0)
  have hqpos : 0 < ‖(q : v.adicCompletion F)‖ := norm_pos_iff.2 hqne
  have hsm : ∀ (m : ℕ) (t : Fin N → v.adicCompletion F), ‖m • t‖ = ‖(m : v.adicCompletion F)‖ * ‖t‖ := by
    intro m t
    rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  refine ⟨{t | r * ‖(q : v.adicCompletion F)‖ ≤ ‖t‖ ∧ ‖t‖ ≤ r}, ?_, ?_, ?_⟩
  · refine (isCompact_closedBall (0 : Fin N → v.adicCompletion F) r).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
    · intro t ht
      simpa [mem_closedBall_zero_iff] using ht.2
  · intro h
    have h1 := h.1
    rw [norm_zero] at h1
    exact absurd h1 (not_le.2 (mul_pos hr hqpos))
  · intro t ht
    have htr : r ≤ ‖t‖ := by
      by_contra hlt
      exact ht (hrV (mem_ball_zero_iff.2 (not_le.1 hlt)))
    have htpos : 0 < ‖t‖ := lt_of_lt_of_le hr htr
    have hex : ∃ k : ℕ, ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := by
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hr htpos) hq1
      exact ⟨k, (lt_div_iff₀ htpos).1 hk⟩
    classical
    set k := Nat.find hex with hkdef
    have hk : ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ < r := Nat.find_spec hex
    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hk
      exact absurd htr (not_le.2 hk)
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hjmin : ¬ ‖(q : v.adicCompletion F)‖ ^ j * ‖t‖ < r :=
      Nat.find_min hex (by omega)
    have hnorm : ‖(q ^ k) • t‖ = ‖(q : v.adicCompletion F)‖ ^ k * ‖t‖ := by
      rw [hsm, Nat.cast_pow, norm_pow]
    refine ⟨q ^ k, ?_, ?_⟩
    · show r * ‖(q : v.adicCompletion F)‖ ≤ ‖(q ^ k) • t‖
      rw [hnorm, hj, pow_succ]
      have := not_lt.1 hjmin
      nlinarith
    · show ‖(q ^ k) • t‖ ≤ r
      rw [hnorm]; exact hk.le

end GlobalTheory.NonarchShell
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag
open GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.WeylCell

namespace GlobalTheory.GKFactor

variable {k : Type} [Field k] {n : ℕ}

theorem weylRep_inv_mul_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    (x⁻¹).val p (w p) * x.val (w p) p = 1 := by
  have h : (x⁻¹ * x).val p p = (1 : GL (Fin n) k).val p p := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single (w p) (fun b _ hb => by rw [hx b p hb, mul_zero]) (by simp)] at h

theorem weylRep_mul_inv_diag {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (p : Fin n) :
    x.val (w p) p * (x⁻¹).val p (w p) = 1 := by
  have h : (x * x⁻¹).val (w p) (w p) = (1 : GL (Fin n) k).val (w p) (w p) := by rw [mul_inv_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_eq] at h
  rwa [Finset.sum_eq_single p (fun b _ hb => by
      rw [hx (w p) b (fun e => hb (w.injective e).symm), zero_mul]) (by simp)] at h

theorem weylRep_inv {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) : IsWeylRep w⁻¹ x⁻¹ := by
  intro p a hpa
  have hne : x.val a (w⁻¹ a) ≠ 0 := by
    intro h0
    have := weylRep_mul_inv_diag hx (w⁻¹ a)
    rw [show w (w⁻¹ a) = a by simp] at this
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have h : (x⁻¹ * x).val p (w⁻¹ a) = (1 : GL (Fin n) k).val p (w⁻¹ a) := by rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Units.val_one, Matrix.one_apply_ne hpa] at h
  rw [Finset.sum_eq_single a (fun b _ hb => by
      rw [hx b (w⁻¹ a) (by simpa using hb), mul_zero]) (by simp)] at h
  exact (mul_eq_zero.1 h).resolve_right hne

theorem weylRep_conj_apply {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k)
    (p q : Fin n) : (x⁻¹ * u * x).val p q = (x⁻¹).val p (w p) * u.val (w p) (w q) * x.val (w q) q := by
  have hi := weylRep_inv hx
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (w q)
    (fun b _ hb => by rw [hx b q hb, mul_zero]) (by simp), Matrix.mul_apply,
    Finset.sum_eq_single (w p) (fun b _ hb => by rw [hi p b (fun e => hb (by rw [e]; simp)), zero_mul]) (by simp)]

theorem mem_cell_iff {w : Equiv.Perm (Fin n)} {x : GL (Fin n) k} (hx : IsWeylRep w x) (u : GL (Fin n) k) :
    u ∈ cell x ↔ u ∈ unipB k (Fin n) ∧ ∀ a b, a < b → w⁻¹ a < w⁻¹ b → u.val a b = 0 := by
  rw [mem_cell, mem_unipBLower]
  refine and_congr_right fun hu => ?_
  rw [mem_unipB] at hu
  constructor
  · rintro ⟨hl, -⟩ a b hab hw
    have h := hl _ _ hw
    rw [weylRep_conj_apply hx, show w (w⁻¹ a) = a by simp, show w (w⁻¹ b) = b by simp] at h
    have h1 := weylRep_inv_mul_diag hx (w⁻¹ a)
    have h2 := weylRep_mul_inv_diag hx (w⁻¹ b)
    rw [show w (w⁻¹ a) = a by simp] at h1
    rw [show w (w⁻¹ b) = b by simp] at h2
    rcases mul_eq_zero.1 h with h | h
    · rcases mul_eq_zero.1 h with h | h
      · rw [h, zero_mul] at h1; exact absurd h1 zero_ne_one
      · exact h
    · rw [h, zero_mul] at h2; exact absurd h2 zero_ne_one
  · intro h
    refine ⟨fun p q hpq => ?_, fun p => ?_⟩
    · rw [weylRep_conj_apply hx]
      rcases lt_or_gt_of_ne (fun e : w p = w q => hpq.ne (w.injective e)) with hl | hl
      · rw [h _ _ hl (by simpa using hpq), mul_zero, zero_mul]
      · rw [hu.1 _ _ hl, mul_zero, zero_mul]
    · rw [weylRep_conj_apply hx, hu.2, mul_one, weylRep_inv_mul_diag hx]

end GlobalTheory.GKFactor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']

def ker (σ : K →ₐ[ℂ] κ') : Ideal (K ⊗[ℂ] κ') :=
  RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))

instance ker_isPrime (σ : K →ₐ[ℂ] κ') : (ker σ).IsPrime := RingHom.ker_isPrime _

theorem mem_ker (σ : K →ₐ[ℂ] κ') (a : K ⊗[ℂ] κ') :
    a ∈ ker σ ↔ Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ') a = 0 := Iff.rfl

theorem primeCompl_le (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]
    (σ : K →ₐ[ℂ] κ') :
    (ker σ).primeCompl ≤ nonZeroDivisors (K ⊗[ℂ] κ') := by
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective _ L)
  intro a ha
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rintro rfl
  exact ha (Ideal.zero_mem _)

variable (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]

def loc (σ : K →ₐ[ℂ] κ') : Subring L :=
  (Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)).toSubring

def toLoc (σ : K →ₐ[ℂ] κ') : K ⊗[ℂ] κ' →+* loc L σ :=
  (algebraMap (K ⊗[ℂ] κ') L).codRestrict (loc L σ) fun a =>
    (Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)).algebraMap_mem a

@[simp] theorem coe_toLoc (σ : K →ₐ[ℂ] κ') (a : K ⊗[ℂ] κ') :
    (toLoc L σ a : L) = algebraMap (K ⊗[ℂ] κ') L a := rfl

instance (σ : K →ₐ[ℂ] κ') : Algebra (K ⊗[ℂ] κ') (loc L σ) := (toLoc L σ).toAlgebra

theorem algebraMap_loc (σ : K →ₐ[ℂ] κ') :
    algebraMap (K ⊗[ℂ] κ') (loc L σ) = toLoc L σ := rfl

instance isLocalization (σ : K →ₐ[ℂ] κ') : IsLocalization.AtPrime (loc L σ) (ker σ) := by
  have h := Localization.subalgebra.isLocalization_ofField L (ker σ).primeCompl (primeCompl_le L σ)
  let S := Localization.subalgebra.ofField L (ker σ).primeCompl (primeCompl_le L σ)
  let e : S ≃ₐ[K ⊗[ℂ] κ'] loc L σ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  exact IsLocalization.isLocalization_of_algEquiv (ker σ).primeCompl e

instance isLocalRing (σ : K →ₐ[ℂ] κ') : IsLocalRing (loc L σ) :=
  IsLocalization.AtPrime.isLocalRing (loc L σ) (ker σ)

theorem map_ker (σ : K →ₐ[ℂ] κ') :
    (ker σ).map (toLoc L σ) = IsLocalRing.maximalIdeal (loc L σ) :=
  IsLocalization.AtPrime.map_eq_maximalIdeal (ker σ) (loc L σ)

end GlobalTheory.DiagLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplex
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
private lemma continuousAt_dbar_ofReal_of_contDiffAt_one {n : ℕ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hρ : ContDiffAt ℝ 1 ρ v) (w : _root_.ReciprocityTheory.L2DbarEstimates.V n) :
    ContinuousAt (fun x => _root_.GlobalTheory.dbar (fun y => (ρ y : ℂ)) x w) v := by
  have h : ContDiffAt ℝ 1 (fun y => (ρ y : ℂ)) v := Complex.ofRealCLM.contDiff.contDiffAt.comp v hρ
  have hf : ContinuousAt (fderiv ℝ (fun y => (ρ y : ℂ))) v :=
    (h.fderiv_right (m := 0) (by norm_num)).continuousAt
  simp only [_root_.GlobalTheory.dbar_apply]
  fun_prop


set_option autoImplicit false in
open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
theorem _root_.GlobalTheory.GoodTop.continuousAt_corrC :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ}
      {G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n},
      ContDiffAt ℝ 1 ρ v → _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₀ v → IsUnit (G₀ v).det →
        _root_.GlobalTheory.HermFrame.MContDiffAt 2 G₁ v → IsUnit (G₁ v).det →
        ContinuousAt (_root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁) v := by
  intro n r _ _ ρ G₀ G₁ v hρ h₀ hd₀ h₁ hd₁
  have hcurv : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a b p q, ContinuousAt (fun x => _root_.GlobalTheory.HermFrame.curv G x (_root_.GlobalTheory.GoodMetric.coordVec a)
        (_root_.GlobalTheory.GoodMetric.coordVec b) p q) v :=
    fun hG hdG a b p q =>
      (hG.curv (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q).continuousAt
  have hconn : ∀ {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ}, _root_.GlobalTheory.HermFrame.MContDiffAt 2 G v → IsUnit (G v).det →
      ∀ a p q, ContinuousAt
        (fun x => _root_.GlobalTheory.HermFrame.conn G x (_root_.GlobalTheory.GoodMetric.coordVec a) p q) v :=
    fun hG hdG a p q =>
      (hG.conn (j := 0) hdG (by norm_num)
        (_root_.GlobalTheory.GoodMetric.coordVec a) p q).continuousAt
  have hposition : ∀ j : Fin n, ContinuousAt (fun x => _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j)) v := by
    intro j
    apply _root_.GlobalTheory.GoodTop.continuousAt_mixTop
    intro i a b p q
    unfold _root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one _root_.GlobalTheory.GoodTop.curvAt _root_.GlobalTheory.GoodTop.cutForm
    split_ifs
    · exact hcurv h₁ hd₁ a b p q
    · exact (continuousAt_dbar_ofReal_of_contDiffAt_one hρ _).mul ((hconn h₁ hd₁ a p q).sub (hconn h₀ hd₀ a p q))
    · exact hcurv h₀ hd₀ a b p q
  have heq : _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ = fun x => ∑ j, _root_.GlobalTheory.GoodTop.mixTop
      (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ x)
        (_root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ x) (_root_.GlobalTheory.GoodTop.curvAt G₀ x) j) := by
    funext x
    rfl
  rw [heq]
  exact tendsto_finsetSum _ fun j _ => hposition j

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtTransgressionTopCoeffComplexStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_transgressionTopCoeffComplex : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, ContDiffAt ℝ 1 ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → ContinuousAt (corrC ρ G₀ G₁) v := by
  first | exact @GlobalTheory.GoodTop.continuousAt_corrC | exact GlobalTheory.GoodTop.continuousAt_corrC | (intros; apply GlobalTheory.GoodTop.continuousAt_corrC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGenerator
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem eq_of_choose_eq_one_of_pos {r D : ℕ} (hD : 0 < D) (h : r.choose D = 1) : D = r := by
  rcases lt_trichotomy D r with hlt | heq | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    rw [Nat.choose_succ_succ] at h
    have h1 := Nat.choose_pos (show d ≤ s by omega)
    have h2 := Nat.choose_pos (show d + 1 ≤ s by omega)
    rw [Nat.succ_eq_add_one] at h
    omega
  · exact heq
  · rw [Nat.choose_eq_zero_of_lt hgt] at h
    exact absurd h zero_ne_one

theorem trBasis_of_isFreeGen_dForm : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L)
    (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
    IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  intro L _ cL Q hQ D x hD hx
  letI := cL.toAlgebra
  let c0 : ℂ →+* Q := cL.codRestrict Q hQ.const_mem
  letI := c0.toAlgebra
  haveI : IsScalarTower ℂ Q L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsFractionRing Q L := IsFractionRing.of_field Q L fun z => by
    obtain ⟨a, ha, b, hb, hb0, e⟩ := hQ.frac z
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    change z = a / b
    rw [eq_div_iff hb0, e]
  haveI : Algebra.FormallyEtale Q L := .of_isLocalization (nonZeroDivisors Q)
  have hL : IsFreeGen L (TopForm.formMap D Q.subtype rfl (dForm c0 x)) :=
    hx.of_isBaseChange (isBaseChange_exteriorPower
      (KaehlerDifferential.isBaseChange_of_formallyEtale ℂ Q L) D)
  rw [TopForm.formMap_dForm] at hL
  change IsFreeGen L (dForm cL fun i => (x i : L)) at hL

  haveI : Algebra.EssFiniteType ℂ Q := hQ.essFiniteType
  haveI : Algebra.EssFiniteType Q L := .of_isLocalization L (nonZeroDivisors Q)
  haveI : Algebra.EssFiniteType ℂ L := .comp ℂ Q L
  have h1 : Module.finrank L (Forms cL D) = 1 := by
    have e : L ≃ₗ[L] Forms cL D := LinearEquiv.ofBijective (LinearMap.toSpanSingleton L _ _) hL
    rw [← e.finrank_eq, Module.finrank_self]
  rw [exteriorPower.finrank_eq] at h1
  have hr := eq_of_choose_eq_one_of_pos hD h1

  have hli : LinearIndependent L fun i => KaehlerDifferential.D ℂ L (x i : L) := by
    by_contra hc
    have h0 : dForm cL (fun i => (x i : L)) = 0 := by
      rw [dForm_eq]
      exact (exteriorPower.ιMulti L D).map_linearDependent _ hc
    rw [h0] at hL
    exact one_ne_zero (hL.1 (a₁ := 1) (a₂ := 0) (by simp))
  have hind : AlgebraicIndependent ℂ fun i => (x i : L) :=
    ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence ℂ L D _ hli
  have htr : Algebra.trdeg ℂ L = D := by
    rw [← rank_kaehler_eq_trdeg, ← Module.finrank_eq_rank]
    exact_mod_cast hr.symm
  exact hind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr, Cardinal.mk_fin])

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisOfKaehlerWedgeFreeGeneratorStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_of_kaehlerWedge_freeGenerator : ∀ {L : Type} [Field L] (cL : ℂ →+* L) (Q : Subring L) (hQ : IsLocModel cL Q) (D : ℕ) (x : Fin D → Q), 0 < D →
  IsFreeGen Q (dForm (cL.codRestrict Q hQ.const_mem) x) → TrBasis cL (fun i => (x i : L)) := by
  first | exact @GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | exact GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm | (intros; apply GlobalTheory.FieldPair.trBasis_of_isFreeGen_dForm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocal
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.EtNormal

theorem isDomain_and_isIntegrallyClosed_of_formallyEtale (A T : Type*) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [IsNoetherianRing A] [CommRing T] [IsLocalRing T] [Algebra A T]
    [Algebra.FormallyEtale A T] [Algebra.EssFiniteType A T] :
    IsDomain T ∧ IsIntegrallyClosed T := by
  let B := Algebra.EssFiniteType.subalgebra A T
  let P : Ideal B := (IsLocalRing.maximalIdeal T).comap (algebraMap B T)
  haveI hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hM : Algebra.EssFiniteType.submonoid A T = P.primeCompl := by
    ext x
    change IsUnit (algebraMap B T x) ↔ x ∉ P
    simp [P, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  haveI hloc : IsLocalization.AtPrime T P := by
    have := Algebra.EssFiniteType.isLocalization A T
    rw [hM] at this
    exact this
  haveI : Algebra.FinitePresentation A B :=
    (Algebra.FinitePresentation.of_finiteType).1 inferInstance
  let e : T ≃ₐ[A] Localization.AtPrime P :=
    (IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars A
  haveI : Algebra.FormallySmooth A (Localization.AtPrime P) := Algebra.FormallySmooth.of_equiv e
  haveI : Algebra.IsSmoothAt A P := inferInstance
  obtain ⟨f, hfP, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := P)
  have := isIntegrallyClosed_mvPolynomial_fin A n
  refine isDomain_and_isIntegrallyClosed_atPrime_of_isLocalization (.powers f)
    (Localization.Away f) P ?_
    (fun q _ ↦ isDomain_and_isIntegrallyClosed_atPrime_of_etale (MvPolynomial (Fin n) A) q _) T
  rwa [Ideal.disjoint_powers_iff_notMem_of_isPrime]

end GlobalTheory.EtNormal

namespace GlobalTheory.FieldPair

theorem isIntegrallyClosed_of_isEtTower : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  intro K L _ _ cK cL r R T ι ψ τ h
  haveI := h.top.isLocalRing
  haveI := h.normal
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let cT : ℂ →+* T := cL.codRestrict T h.top.const_mem
  letI : Algebra ℂ R := c0.toAlgebra
  haveI : Algebra.EssFiniteType ℂ R := h.base.essFiniteType
  haveI : IsNoetherianRing R := Algebra.EssFiniteType.isNoetherianRing ℂ R
  let A := MvPolynomial (Fin r) R
  let φ : A →+* T := MvPolynomial.eval₂Hom ι τ
  letI : Algebra A T := φ.toAlgebra
  letI : Algebra ℂ T := cT.toAlgebra
  haveI : Algebra.FormallyEtale A T := h.etale
  haveI : Algebra.EssFiniteType ℂ T := h.top.essFiniteType
  haveI : IsScalarTower ℂ A T := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    change cT a = φ (MvPolynomial.C (c0 a))
    have e : φ (MvPolynomial.C (c0 a)) = ι (c0 a) := MvPolynomial.eval₂Hom_C _ _ _
    rw [e]
    exact Subtype.ext (h.const a).symm
  haveI : Algebra.EssFiniteType A T := Algebra.EssFiniteType.of_comp ℂ A T
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_mvPolynomial_fin R r
  exact (GlobalTheory.EtNormal.isDomain_and_isIntegrallyClosed_of_formallyEtale A T).2

end GlobalTheory.FieldPair
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedOfIsEtaleTowerOverNormalLocalStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegrallyClosed_of_isEtaleTowerOverNormalLocal : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T), IsEtTower cK R cL T ι ψ τ → IsIntegrallyClosed T := by
  first | exact @GlobalTheory.FieldPair.isIntegrallyClosed_of_isEtTower | exact GlobalTheory.FieldPair.isIntegrallyClosed_of_isEtTower | (intros; apply GlobalTheory.FieldPair.isIntegrallyClosed_of_isEtTower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInte
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodConj

theorem eventually_mem_integers {E : Type} [Field E] [NumberField E] (a : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w (n := n) := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w →
      ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  intro E _ _ _ _ n _ γ hsep
  have hint : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) ((γ.1 : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E ∧
      algebraMap E (w.adicCompletion E) (((γ.1 : GL (Fin n) E)⁻¹).val i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (eventually_mem_integers _).and (eventually_mem_integers _)
  filter_upwards [hint, GlobalTheory.T.eventually_integral_lift_coprime_derivative E _ hsep] with w hw hP
  obtain ⟨P₀, hP₀, hcop⟩ := hP
  intro g hg
  set y : GLw n w := Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ.1 : GL (Fin n) E) with hy
  by_cases hmem : y ∈ UL n w
  · have hloc : ((locPt w γ : UL n w) : GLw n w) = y := by
      simp only [locPt, toSub]
      rw [dite_eq_left hmem]
    have hyK : y ∈ GlobalTheory.LFun.KGL w (n := n) := by
      apply mem_KGL_of_entries
      · intro a b; exact (hw a b).1
      · intro a b
        rw [hy, ← map_inv]
        exact (hw a b).2
    have hK : locPt w γ ∈ KL n w := by
      rw [KL, Subgroup.mem_subgroupOf, hloc]; exact hyK
    obtain ⟨h1, h2⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
    have hcp : (locPt w γ).1.val.charpoly =
        P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
      rw [hloc, hP₀, hy]
      exact Matrix.charpoly_map _ _
    obtain ⟨t, ht, k, hk, he⟩ := GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w h1 h2 P₀ hcop (locPt w γ) hcp 1 g
      (by simpa using hK) hg
    refine ⟨t, ht, ?_⟩
    rw [he, mul_one, inv_mul_cancel_left]
    exact hk
  · have hloc : locPt w γ = 1 := by
      simp only [locPt, toSub]
      rw [dite_eq_right hmem]
    refine ⟨g, ?_, by rw [inv_mul_cancel]; exact one_mem _⟩
    rw [hloc]
    show g * 1 = 1 * (MonoidHom.id _) g
    simp

end GlobalTheory.BCT.GoodConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralConjugateMemCentralizerMulInteStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integralConjugate_mem_centralizer_mul_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w → ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  first | exact @GlobalTheory.BCT.GoodConj.main | exact GlobalTheory.BCT.GoodConj.main | (intros; apply GlobalTheory.BCT.GoodConj.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaValuesCoefficientExists
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift

namespace GlobalTheory.GalLift.BaseDatum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def along {K X Z : Type} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module ℂ Z] {s s' : K →+* ℂ} (h : s = s')
    (f : X →ₛₗ[s] Z) : X →ₛₗ[s'] Z where
  toFun := f
  map_add' := f.map_add
  map_smul' a x := by rw [← h]; exact f.map_smulₛₗ a x

theorem ext_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (hact : ∀ γ, ∃ T : M → M, ∀ v, c₀ (T v) = ρ γ (c₀ v))
    (hχ : ∀ k, ∃ y, σ₀ y = ((χ k : ℂˣ) : ℂ)) (f : S.Cl → S.V) (h : G) : ∃ v, P.ext f h = c₀ v := by
  obtain ⟨T, hT⟩ := hact (P.decG h)
  obtain ⟨y, hy⟩ := hχ (P.decK h)
  refine ⟨y • T (e (f (P.decC h))), ?_⟩
  rw [map_smulₛₗ, hT, hy, ← he]
  rfl

theorem pair_val {G Γ W K M : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [Field K] [NumberField K] [StarRing K] [AddCommGroup M] [Module K M] {ι : Γ →* G} {S : CSD K} {σ₀ : K →+* ℂ}
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} (P : Bridge.ClassPres ι S σ₀ ρ J χ)
    (c₀ : M →ₛₗ[σ₀] W) (e : S.V ≃ₗ[K] M) (he : ∀ x, P.coef x = c₀ (e x))
    (pr : M → M → K) (hp : ∀ x x', pr (e x) (e x') = S.pair x x') (v w : M) :
    inner ℂ (c₀ v) (c₀ w) = σ₀ (pr v w) := by
  have h := P.coef_pair (e.symm v) (e.symm w)
  rw [he, he, ← hp] at h
  simpa only [LinearEquiv.apply_symm_apply] using h

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

include R in
theorem realisation_embedding_eq_baseEmbedding : D.what₂.embLL = sg0 D A := (sgAt_mk _ R.hv0).symm

theorem isEtaConj_base (hL : R.toLevCh.Is A.μ0) (hV : EtaVals R) : IsEtaConj (sg0 D A) R.eta R.eta :=
  ⟨hL.eta.1, GlobalTheory.EtaConjExist.unram_of_chrEq hL.eta R.C.isEta.unr, fun P e he x hx =>
    (hV P e he x hx).imp fun y hy => ⟨hy, (RingHom.congr_fun (realisation_embedding_eq_baseEmbedding R) y).symm.trans hy⟩⟩


theorem places_base (hL : R.toLevCh.Is A.μ0) : R.Q A.μ0 = ∅ :=
  Finset.eq_empty_iff_forall_notMem.2 fun PP hPP =>
    (hL.Q_ram A.μ0 PP).2 (Or.inl hPP) (by rw [hL.xi_base]; exact fun _ _ => rfl)

theorem mu_base (hL : R.toLevCh.Is A.μ0) (j : ℕ) : R.toLevCh.mu A.μ0 j = R.mu0 j := by
  have hxi : R.xi A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi A.μ0))
  exact (congrArg (R.mu0 j * ·) hxi).trans (mul_one _)

theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dite_eq_left (by simp)]
  simp

theorem isThPVecOf_empty {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {sS sT ΛS ΛT βS βT}
    {Pg Q : Finset (Pl D.host.E)} (hQ : Q = ∅) {ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    {f₀ f : WO S T → ℂ} (h : IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg Q ξ f₀ f) :
    IsThPVecOf ψ θ S T sS sT ΛS ΛT βS βT Pg ∅ ξ' f₀ f := by
  subst hQ
  unfold IsThPVecOf at h ⊢
  simp only [omegaQ_empty] at h ⊢
  exact h

include R in
theorem deltaConj_base : deltaConj i (sg0 D A) = RealDat.Delta i := by
  have hl : lab (sg0 D A) = id := by
    rw [← realisation_embedding_eq_baseEmbedding R]; exact funext GlobalTheory.IndefiniteRowSideFullHecke.LiftFormsMainTerm.lab_base
  unfold deltaConj
  rw [hl]
  rfl


end GlobalTheory.GalLift.BaseDatum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelsEvaluateSecond
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, Finset.sum_apply] using h q

end GlobalTheory.GalLift.BaseId

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion

namespace GlobalTheory.RatFix

theorem ratfix_mul_eq (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E) (hBA : B₀ * A₀ = 1) (G : Matrix (Fin M) (Fin M) (R ⊗[F] E))
    (hG : ∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) :
    G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  set ι : E →+* R ⊗[F] E := inclR (F := F) R with hι
  have hN : (1 : Matrix (Fin M) (Fin M) (R ⊗[F] E)) - A₀.map ι * B₀.map ι = (1 - A₀ * B₀).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_mul, Matrix.map_one _ (map_zero ι) (map_one ι)]
  rw [hN]
  have hBN : B₀ * (1 - A₀ * B₀) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hBA, Matrix.one_mul, sub_self]
  ext i j
  have hv : B₀.mulVec (fun k => ((1 : Matrix (Fin M) (Fin M) E) - A₀ * B₀) k j) = 0 := by
    funext a
    have := congrFun (congrFun hBN a) j
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  have := congrFun (hG _ hv) i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this

theorem ratfix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) :=
  fun F E _ _ _ R _ _ M A₀ B₀ hBA G hG => ratfix_mul_eq F E R M A₀ B₀ hBA G hG

end GlobalTheory.RatFix
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixFixesLowRankProjectorOfFixesRationalKernelStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published GlobalTheory.QSA GlobalTheory.PlaneSU
open scoped TensorProduct Quaternion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_fixes_lowRankProjector_of_fixes_rationalKernel : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (M : ℕ) (A₀ : Matrix (Fin M) (Fin 2) E) (B₀ : Matrix (Fin 2) (Fin M) E), B₀ * A₀ = 1 → ∀ G : Matrix (Fin M) (Fin M) (R ⊗[F] E), (∀ v : Fin M → E, B₀.mulVec v = 0 → G.mulVec (fun i => inclR (F := F) R (v i)) = fun i => inclR (F := F) R (v i)) → G * (1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R)) = 1 - A₀.map (inclR (F := F) R) * B₀.map (inclR (F := F) R) := by
  first | exact @GlobalTheory.RatFix.ratfix | exact GlobalTheory.RatFix.ratfix | (intros; apply GlobalTheory.RatFix.ratfix <;> assumption)
end
end
