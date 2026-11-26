module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableCoordinateMap
section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasMUpper
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OF

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem measM_lowP {X : Type*} [MeasurableSpace X] {m : ℕ} (w : Equiv.Perm (Fin m)) {y : X → C2.LPidx w → ℂ}
    (hy : Measurable y) : MeasM (fun x => lowP w (y x)) := by
  rw [measM_iff]
  intro i j
  simp only [lowP, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
  refine measurable_const.add (Finset.measurable_sum _ fun q _ => ?_)
  split_ifs
  · exact (measurable_pi_apply q).comp hy
  · exact measurable_const

theorem measM_upper {X : Type*} [MeasurableSpace X] {m : ℕ} {u : X → G.UT m → ℂ} (hu : Measurable u) :
    MeasM (fun x => G.upper (u x)) := by
  rw [measM_iff]
  intro i j
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply]
  refine measurable_const.add ?_
  split_ifs with h
  · exact (measurable_pi_apply _).comp hu
  · exact measurable_const

theorem measM_uMap {X : Type*} [MeasurableSpace X] (z : Fin (2 * r + k + 1) → ℂ) {A : X → B.Mat k r}
    (hA : MeasM A) : MeasM (fun x => C2.uMap k r z (A x)) := by
  have h := measM_of_cont
    (f := fun y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ => C2.uMap k r z (Matrix.of y))
    (g := fun x => Matrix.of.symm (A x)) ?_ hA
  · simpa only [Equiv.apply_symm_apply] using h
  · refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [C2.uMap, herm, Matrix.of_symm_apply]
    split_ifs
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop

theorem meas_utc {X : Type*} [MeasurableSpace X] {m : ℕ} {A : X → Matrix (Fin m) (Fin m) ℂ} (hA : MeasM A) :
    Measurable fun x => utc (A x) := by
  rw [measM_iff] at hA
  exact Measurable.of_eval fun q => hA q.1.1 q.1.2

section main

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)

include hγ hd hZw hpos in
theorem measM_rhoX {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x) :
    MeasM (fun t => rhoX S γ w (x t)) := by
  have hg : Dx2.Rad.Good S γ w d := by
    first
    | exact good S hγ hd hZw hpos
    | exact good S hγ hd hZw
    | exact good S hγ hZw hd
  obtain ⟨-, hinj, -⟩ := hg
  have hs : ∀ x, rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := fun x => by
    first
    | exact rhoX_spec S hγ hd hZw hpos x
    | exact rhoX_spec S hγ hd hZw x

  have hR : IsClosed (C6.Rset γ) := by
    have hN : IsClosed (Nset k r) := (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed
    have hc : Continuous fun ρ : B.Mat k r => γ⁻¹ * ρ * γ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have h2 : IsClosed ((fun ρ : B.Mat k r => γ⁻¹ * ρ * γ) ⁻¹' Nset k r) := hN.preimage hc
    have h3 : C6.Rset γ = Nset k r ∩ ((fun ρ : B.Mat k r => γ⁻¹ * ρ * γ) ⁻¹' Nset k r) := by
      ext ρ
      simp only [C6.Rset, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    rw [h3]
    exact hN.inter h2
  set R' : Set (Mt k r) := {y | Matrix.of y ∈ C6.Rset γ} with hR'def
  have hR' : IsClosed R' := hR.preimage continuous_id
  set F : Mt k r → Fin (r + 1) → Fin (r + 1) → ℂ := fun y => Matrix.of.symm (C2.uMap k r S.z (Matrix.of y))
    with hFdef
  have hF : Continuous F := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [hFdef, C2.uMap, herm, Matrix.of_symm_apply]
    split_ifs
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
    · simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
      fun_prop
  set H : (C2.Lstidx w → ℂ) → Fin (r + 1) → Fin (r + 1) → ℂ := fun x => Matrix.of.symm ((lowS w x)ᴴ) with hHdef
  have hlow : MeasM (fun x : C2.Lstidx w → ℂ => lowS w x) := by
    rw [measM_iff]
    intro i j
    simp only [lowS, C2.lowOf, Matrix.add_apply, Matrix.of_apply]
    refine measurable_const.add (Finset.measurable_sum _ fun q _ => ?_)
    split_ifs
    · exact measurable_pi_apply q
    · exact measurable_const
  have hH : Measurable H := measM_star hlow
  have hΦ : Measurable fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoX S γ w x) : Mt k r) := by
    intro B hB
    have hset : (fun x : C2.Lstidx w → ℂ => (Matrix.of.symm (rhoX S γ w x) : Mt k r)) ⁻¹' B =
        H ⁻¹' (F '' (B ∩ R')) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_image, Set.mem_inter_iff]
      constructor
      · intro hx
        refine ⟨Matrix.of.symm (rhoX S γ w x), ⟨hx, ?_⟩, ?_⟩
        · simpa only [hR'def, Set.mem_setOf_eq, Equiv.apply_symm_apply] using (hs x).1
        · simp only [hFdef, hHdef, Equiv.apply_symm_apply, (hs x).2]
      · rintro ⟨y, ⟨hyB, hyR⟩, hFy⟩
        have hyR2 : Matrix.of y ∈ C6.Rset γ := hyR
        have hu : C2.uMap k r S.z (Matrix.of y) = C2.uMap k r S.z (rhoX S γ w x) := by
          rw [(hs x).2]
          exact Matrix.of.symm.injective hFy
        have := hinj hyR2 (hs x).1 hu
        rw [← this]
        simpa using hyB
    rw [hset]
    exact hH (MeasurableSet.image_of_continuousOn_injOn (hB.inter hR'.measurableSet) hF.continuousOn
      (fun a ha b hb hab => by
        have h1 : Matrix.of a ∈ C6.Rset γ := ha.2
        have h2 : Matrix.of b ∈ C6.Rset γ := hb.2
        have := hinj h1 h2 (Matrix.of.symm.injective hab)
        simpa using this))
  exact hΦ.comp hx

include hγ hd hZw hpos in
theorem measM_rhoP {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x) :
    MeasM (fun t => rhoP S γ w (x t)) := by
  simp only [rhoP]
  exact measM_mul (measM_mul (measM_const _) (measM_inv (measM_rhoX S hγ hd hZw hpos hx))) (measM_const _)

include hγ hd hZw hpos in
theorem measM_m0L {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x)
    {y : X → C2.LPidx w → ℂ} (hy : Measurable y) : MeasM (fun t => m0L S γ w e (x t) (y t)) := by
  simp only [m0L]
  have hxy : Measurable fun t => (x t, y t) := hx.prodMk hy
  exact measM_mul (measM_mul (measM_inv (measM_tau _ (measM_star (measM_lowP w hy))))
    (measM_inv (measM_rhoX S hγ hd hZw hpos hx))) (measM_tau _ (measM_upper (e.measurable.comp hxy)))

include hγ hd hZw hpos in
theorem measM_m0R {X : Type*} [MeasurableSpace X] {x : X → C2.Lstidx w → ℂ} (hx : Measurable x)
    {u : X → G.UT (r + 1) → ℂ} (hu : Measurable u) : MeasM (fun t => m0R S γ w (x t) (u t)) := by
  simp only [m0R]
  have hP := measM_rhoP S hγ hd hZw hpos hx
  exact measM_mul (measM_mul (measM_inv (measM_tau _ (measM_mul (measM_uMap _ hP) (measM_upper hu)))) hP)
    (measM_tau _ (measM_upper hu))

include hγ hd hZw hpos in
theorem meas_Tx : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => Tx S γ w e p.1 p.2 := by
  have h1 : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.1 := measurable_fst
  have hy : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.1.2.1 := by fun_prop
  have hu : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.2.2.1 := by fun_prop
  have hM : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w => Matrix.of p.2.1.2.2 := by
    unfold MeasM
    simp only [Equiv.symm_apply_apply]
    fun_prop
  have hM' : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w => Matrix.of p.2.2.2.2 := by
    unfold MeasM
    simp only [Equiv.symm_apply_apply]
    fun_prop
  have hA : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      Matrix.of.symm (m0L S γ w e p.1 p.2.1.2.1 * Matrix.of p.2.1.2.2) :=
    measM_mul (measM_m0L S hγ hd hZw hpos e h1 hy) hM
  have hB : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      utc (C2.uMap k r S.z' (rhoP S γ w p.1) * G.upper p.2.2.2.1) :=
    meas_utc (measM_mul (measM_uMap _ (measM_rhoP S hγ hd hZw hpos h1)) (measM_upper hu))
  have hC : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      Matrix.of.symm (m0R S γ w p.1 p.2.2.2.1 * Matrix.of p.2.2.2.2) :=
    measM_mul (measM_m0R S hγ hd hZw hpos h1 hu) hM'
  have ha : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.1.1 := by fun_prop
  have hb : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => p.2.2.1 := by fun_prop
  exact (ha.prodMk (hy.prodMk hA)).prodMk (hb.prodMk ((hB.prodMk hC)))

include hγ hd hZw hpos in
theorem upperUnipotent_mem_upperTriangular (x : C2.Lstidx w → ℂ) : C2.uMap k r S.z' (rhoP S γ w x) ∈ C2.UTset (r + 1) := by
  have h := (by apply uP_UT <;> assumption :
    C2.uMap k r S.z' (rhoP S γ w x) * G.upper (0 : G.UT (r + 1) → ℂ) ∈ C2.UTset (r + 1))
  have h0 : G.upper (0 : G.UT (r + 1) → ℂ) = 1 := by
    ext i j
    simp [G.upper, G.strictUpper]
  rwa [h0, mul_one] at h

variable {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hγ hd hZw hpos he hμ0 hμ0' in
theorem mp_Tx (x : C2.Lstidx w → ℂ) : MeasurePreserving (Tx S γ w e x) (nuR S w μ0 μ0') (nuR S w μ0 μ0') := by
  have sf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := sf hμ0
  haveI := sf hμ0'
  haveI := sf S.haarW
  haveI := sf S.haarW'
  have hL : MeasurePreserving
      (fun p : (C2.LPidx w → ℂ) × Mt k r => (id p.1, lmulM (m0L S γ w e x p.1) p.2))
      ((volume : Measure (C2.LPidx w → ℂ)).prod μ0) ((volume : Measure (C2.LPidx w → ℂ)).prod μ0) := by
    refine MeasurePreserving.skew_product (μc := μ0) (μd := μ0)
      (g := fun y M => lmulM (m0L S γ w e x y) M) (MeasurePreserving.id (volume : Measure (C2.LPidx w → ℂ))) ?_
      (Filter.Eventually.of_forall fun y => ?_)
    · have h := measM_mul (measM_m0L S hγ hd hZw hpos e (measurable_const (a := x)) measurable_fst)
        (show MeasM fun p : (C2.LPidx w → ℂ) × Mt k r => Matrix.of p.2 by
          unfold MeasM
          simp only [Equiv.symm_apply_apply]
          fun_prop)
      exact h
    · exact hμ0.left _ (by apply left_stabilizer_mem <;> assumption)
  have hR : MeasurePreserving
      (fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        (utc (C2.uMap k r S.z' (rhoP S γ w x) * G.upper p.1), lmulM (m0R S γ w x p.1) p.2))
      ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0') ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0') := by
    refine MeasurePreserving.skew_product (μc := μ0') (μd := μ0')
      (g := fun u M => lmulM (m0R S γ w x u) M) (Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.mp_UTleft (upperUnipotent_mem_upperTriangular S hγ hd hZw hpos x)) ?_

      (Filter.Eventually.of_forall fun u => ?_)
    · have h := measM_mul (measM_m0R S hγ hd hZw hpos (measurable_const (a := x)) measurable_fst)
        (show MeasM fun p : (G.UT (r + 1) → ℂ) × Mt k r => Matrix.of p.2 by
          unfold MeasM
          simp only [Equiv.symm_apply_apply]
          fun_prop)
      exact h
    · exact hμ0'.left _ (by apply right_stabilizer_mem <;> assumption)
  have hall := ((MeasurePreserving.id S.μW).prod hL).prod ((MeasurePreserving.id S.μW').prod hR)
  exact hall

include hγ hd hZw hpos he hμ0 hμ0' in
theorem mp_Tt : MeasurePreserving (Tt S γ w e) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0'))
    ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
  have sf : ∀ {U : Set (B.Mat k r)} {μ : Measure (Mt k r)}, B.IsHaarOn U μ → SigmaFinite μ := by
    intro U μ h
    haveI : IsFiniteMeasureOnCompacts μ := ⟨h.finite_compact⟩
    infer_instance
  haveI := sf hμ0
  haveI := sf hμ0'
  haveI := sf S.haarW
  haveI := sf S.haarW'
  haveI : SFinite (nuR S w μ0 μ0') := by
    unfold nuR
    infer_instance
  have h := MeasurePreserving.skew_product (μc := nuR S w μ0 μ0') (μd := nuR S w μ0 μ0')
    (g := fun x q => Tx S γ w e x q) (MeasurePreserving.id (volume : Measure (C2.Lstidx w → ℂ)))
    (meas_Tx S hγ hd hZw hpos e)
    (Filter.Eventually.of_forall fun x => (mp_Tx S hγ hd hZw hpos e he hμ0 hμ0' x).map_eq)
  exact h

include hγ hd hZw hpos he in
theorem inj_Tt : Function.Injective (Tt S γ w e) := by
  rintro ⟨x, ⟨a, y, M⟩, ⟨b, u, M'⟩⟩ ⟨x', ⟨a', y', N⟩, ⟨b', u', N'⟩⟩ h
  simp only [Tt, Tx, Prod.mk.injEq] at h
  obtain ⟨rfl, ⟨rfl, rfl, hM⟩, rfl, hu, hM'⟩ := h
  have hc : C2.uMap k r S.z' (rhoP S γ w x) ∈ C2.UTset (r + 1) := upperUnipotent_mem_upperTriangular S hγ hd hZw hpos x
  have hcu : IsUnit (C2.uMap k r S.z' (rhoP S γ w x)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have hdet : (C2.uMap k r S.z' (rhoP S γ w x)).det = 1 := by
      rw [Matrix.det_of_upperTriangular (fun i j hij => hc.1 i j hij)]
      simp [hc.2]
    rw [hdet]
    exact isUnit_one
  have hU : ∀ v : G.UT (r + 1) → ℂ, C2.uMap k r S.z' (rhoP S γ w x) * G.upper v ∈ C2.UTset (r + 1) :=
    fun v => by apply uP_UT <;> assumption
  have huu : u = u' := by
    have hmat : C2.uMap k r S.z' (rhoP S γ w x) * G.upper u = C2.uMap k r S.z' (rhoP S γ w x) * G.upper u' := by
      ext i j
      rcases lt_trichotomy i j with hij | rfl | hij
      · simpa [utc] using congrFun hu ⟨(i, j), hij⟩
      · rw [(hU u).2 i, (hU u').2 i]
      · rw [(hU u).1 i j hij, (hU u').1 i j hij]
    have hup := hcu.mul_left_cancel hmat
    rw [← Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.utc_upper u, ← Formalism.FourierDecayAlt.P.StabilizerDisintegration.HC.utc_upper u', hup]
  subst huu
  have hL : IsUnit (m0L S γ w e x y) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit _ (by apply left_stabilizer_mem <;> assumption : m0L S γ w e x y ∈ C2.N0set k r S.z).1
  have hR : IsUnit (m0R S γ w x u) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).unit _ (by apply right_stabilizer_mem <;> assumption : m0R S γ w x u ∈ C2.N0set k r S.z').1
  have e1 : Matrix.of M = Matrix.of N := hL.mul_left_cancel (Matrix.of.symm.injective hM)
  have e2 : Matrix.of M' = Matrix.of N' := hR.mul_left_cancel (Matrix.of.symm.injective hM')
  simp only [EmbeddingLike.apply_eq_iff_eq] at e1 e2
  subst e1
  subst e2
  rfl

set_option synthInstance.maxHeartbeats 400000 in
include hγ hd hZw hpos he in
theorem emb_Tt : MeasurableEmbedding (Tt S γ w e) := set_option maxHeartbeats 800000 in by
  have hm : Measurable (Tt S γ w e) := by
    unfold Tt
    exact measurable_fst.prodMk (meas_Tx S hγ hd hZw hpos e)
  have hi : Function.Injective (Tt S γ w e) := inj_Tt S hγ hd hZw hpos e he
  haveI i1 : StandardBorelSpace (C2.Lstidx w → ℂ) := inferInstance
  haveI i2 : StandardBorelSpace (Mt k r) := inferInstance
  haveI i3 : StandardBorelSpace (G.UT (r + 1) → ℂ) := inferInstance
  haveI i4 : StandardBorelSpace (C2.LPidx w → ℂ) := inferInstance
  haveI i5 : StandardBorelSpace (RR k r w) := inferInstance
  haveI i6 : StandardBorelSpace ((C2.Lstidx w → ℂ) × RR k r w) := inferInstance
  exact hm.measurableEmbedding hi

end main

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OF
end

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OG

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD Formalism.FourierDecayAlt.P.StabilizerDisintegration.MM
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

section meas

variable (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1)))
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ))

theorem meas_Xi : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => Xi S w e p.1 p.2 := by
  have he : Measurable fun p : (C2.Lstidx w → ℂ) × RR k r w => e (p.1, p.2.1.2.1) :=
    e.measurable.comp (measurable_fst.prodMk measurable_snd.fst.snd.fst)
  have h1 : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      C2.tauM k r S.z (G.upper (e (p.1, p.2.1.2.1))) * Matrix.of p.2.1.2.2 :=
    measM_mul (measM_tau _ (OF.measM_upper he)) measurable_snd.fst.snd.snd
  have h2 : MeasM fun p : (C2.Lstidx w → ℂ) × RR k r w =>
      C2.tauM k r S.z' (G.upper p.2.2.2.1) * Matrix.of p.2.2.2.2 :=
    measM_mul (measM_tau _ (OF.measM_upper measurable_snd.snd.snd.fst)) measurable_snd.snd.snd.snd
  exact (measurable_snd.fst.fst.prodMk h1).prodMk (measurable_snd.snd.fst.prodMk h2)

variable {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hμ0 hμ0' in
theorem ae_good : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.1 ∈ UWset k r S.z ∧ Matrix.of q.1.2.2 ∈ C2.N0set k r S.z ∧
    Matrix.of q.2.1 ∈ UWset k r S.z' ∧ Matrix.of q.2.2.2 ∈ C2.N0set k r S.z' := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  have hW : ∀ᵐ a ∂S.μW, Matrix.of a ∈ UWset k r S.z :=
    ae_iff.2 S.haarW.conc
  have hW' : ∀ᵐ a ∂S.μW', Matrix.of a ∈ UWset k r S.z' :=
    ae_iff.2 S.haarW'.conc
  have hN : ∀ᵐ a ∂μ0, Matrix.of a ∈ C2.N0set k r S.z :=
    ae_iff.2 hμ0.conc
  have hN' : ∀ᵐ a ∂μ0', Matrix.of a ∈ C2.N0set k r S.z' :=
    ae_iff.2 hμ0'.conc
  have a1 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.1 ∈ UWset k r S.z := by
    have b1 : ∀ᵐ p ∂(S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)), Matrix.of p.1 ∈ UWset k r S.z :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun a : Mt k r => Matrix.of a ∈ UWset k r S.z) hW
    exact Measure.quasiMeasurePreserving_fst.ae (p := fun p : Mt k r × ((C2.LPidx w → ℂ) × Mt k r) =>
      Matrix.of p.1 ∈ UWset k r S.z) b1
  have a2 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.1.2.2 ∈ C2.N0set k r S.z := by
    have b1 : ∀ᵐ p ∂((volume : Measure (C2.LPidx w → ℂ)).prod μ0), Matrix.of p.2 ∈ C2.N0set k r S.z :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun a : Mt k r => Matrix.of a ∈ C2.N0set k r S.z) hN
    have b2 : ∀ᵐ p ∂(S.μW.prod ((volume : Measure (C2.LPidx w → ℂ)).prod μ0)),
        Matrix.of p.2.2 ∈ C2.N0set k r S.z :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun p : (C2.LPidx w → ℂ) × Mt k r =>
        Matrix.of p.2 ∈ C2.N0set k r S.z) b1
    exact Measure.quasiMeasurePreserving_fst.ae (p := fun p : Mt k r × ((C2.LPidx w → ℂ) × Mt k r) =>
      Matrix.of p.2.2 ∈ C2.N0set k r S.z) b2
  have a3 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.2.1 ∈ UWset k r S.z' := by
    have b1 : ∀ᵐ p ∂(S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')),
        Matrix.of p.1 ∈ UWset k r S.z' :=
      Measure.quasiMeasurePreserving_fst.ae (p := fun a : Mt k r => Matrix.of a ∈ UWset k r S.z') hW'
    exact Measure.quasiMeasurePreserving_snd.ae (p := fun p : Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r) =>
      Matrix.of p.1 ∈ UWset k r S.z') b1
  have a4 : ∀ᵐ q ∂(nuR S w μ0 μ0'), Matrix.of q.2.2.2 ∈ C2.N0set k r S.z' := by
    have b1 : ∀ᵐ p ∂((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0'), Matrix.of p.2 ∈ C2.N0set k r S.z' :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun a : Mt k r => Matrix.of a ∈ C2.N0set k r S.z') hN'
    have b2 : ∀ᵐ p ∂(S.μW'.prod ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0')),
        Matrix.of p.2.2 ∈ C2.N0set k r S.z' :=
      Measure.quasiMeasurePreserving_snd.ae (p := fun p : (G.UT (r + 1) → ℂ) × Mt k r =>
        Matrix.of p.2 ∈ C2.N0set k r S.z') b1
    exact Measure.quasiMeasurePreserving_snd.ae (p := fun p : Mt k r × ((G.UT (r + 1) → ℂ) × Mt k r) =>
      Matrix.of p.2.2 ∈ C2.N0set k r S.z') b2
  filter_upwards [a1, a2, a3, a4] with q h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

end meas

theorem nn_smul {α : Type*} [MeasurableSpace α] (c : NNReal) (μ : Measure α) : c • μ = ((c : ENNReal) • μ) := by
  ext s _
  rw [Measure.smul_apply, Measure.smul_apply]
  rfl

theorem meas_actR (γ : B.Mat k r) (p : B.SS k r) :
    Measurable fun y : Mt k r => C6.actR γ (Matrix.of y) p := by
  have hy : MeasM fun y : Mt k r => Matrix.of y := measurable_id
  unfold C6.actR
  exact (measurable_const.prodMk (measM_mul hy (measM_const _))).prodMk
    (measurable_const.prodMk (measM_mul (measM_mul (measM_mul (measM_const _) hy) (measM_const _)) (measM_const _)))

def Hf (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1))) (θ : B.SS k r → ℝ)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (p : (C2.Lstidx w → ℂ) × RR k r w) : Wq →L[ℂ] Wp :=
  θ (C6.actR γ (rhoX S γ w p.1) (Xi0 S w p.2)) • D.orbIntegrand S γ F (Xi0 S w p.2)

section main

variable (S : B.RealPlaceData k r Wp Wq) {γ : B.Mat k r} (hγ : γ ∈ B.GV k r) {w : Equiv.Perm (Fin (r + 1))}
  {d : Fin (r + 1) → ℂ} (hd : ∀ a, d a ≠ 0) (hZw : Zhat k r S.z S.z' γ = C2.monoP w d)
  (hpos : 0 < Gf k r S.z S.z' γ) (hrel : C6.IsRelevant S γ)
  (e : ((C2.Lstidx w → ℂ) × (C2.LPidx w → ℂ)) ≃ᵐ (G.UT (r + 1) → ℂ)) (hemp : MeasurePreserving e volume volume)
  (he : ∀ p, G.upper (e p) = (lowS w p.1)ᴴ * (lowP w p.2)ᴴ)
  {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
  (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0')

include hγ hd hZw hpos hrel he in
theorem comp_eq (θ : B.SS k r → ℝ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (x : C2.Lstidx w → ℂ) (q : RR k r w)
    (hq1 : Matrix.of q.1.2.2 ∈ Nset k r) (hq2 : Matrix.of q.2.2.2 ∈ Nset k r) :
    θ (Xi S w e x q) • D.orbIntegrand S γ F (Xi S w e x q) = Hf S γ w θ F (Tt S γ w e (x, q)) := by
  have key : ∀ {ρ : B.Mat k r}, ρ ∈ C6.Rset γ → ∀ (p : B.SS k r), WeylGroupFacts.col k r (Matrix.of p.1.2) →
      WeylGroupFacts.col k r (Matrix.of p.2.2) → D.orbIntegrand S γ F (C6.actR γ ρ p) = D.orbIntegrand S γ F p := by
    intro ρ hρ p h1 h2
    have hψ := hrel.2 ρ hρ
    obtain ⟨hρN, hρ'N⟩ := hρ
    have cρ := ((WeylGroupFacts.nset_iff _).1 hρN).2
    have cρ' := ((WeylGroupFacts.nset_iff _).1 hρ'N).2
    have iρ : ρ⁻¹ * ρ = 1 := PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρN).1
    have iγ : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ (Matrix.isUnit_det_of_left_inverse (PI.PolynomialProperness.GN.inv_mul hγ))
    have e1 := WeylGroupFacts.ell_mul S.z S.z_mem cρ h1
    have e2 := WeylGroupFacts.ell_mul S.z' S.z'_mem cρ' h2
    have hs : (Matrix.of p.1.1)⁻¹ * (ρ * Matrix.of p.1.2)⁻¹ * γ * (γ⁻¹ * ρ * γ * Matrix.of p.2.2) * Matrix.of p.2.1 =
        (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 := by
      rw [Matrix.mul_inv_rev]
      calc _ = (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * (ρ⁻¹ * (γ * γ⁻¹) * ρ) * γ * Matrix.of p.2.2 *
            Matrix.of p.2.1 := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [iγ, Matrix.mul_one, iρ, Matrix.mul_one]
    have hxi : B.xiTau S (1, 1) (C6.actR γ ρ p) = B.xiTau S (1, 1) p := by
      unfold B.xiTau C6.actR
      simp only [Equiv.apply_symm_apply]
      unfold B.lam
      rw [e1, e2]
      unfold psi at hψ
      set a := (cStd * ell k r S.z ρ).re
      set b := (cStd * ell k r S.z' (γ⁻¹ * ρ * γ)).re
      have hx : ((1 : ℝ) * (cStd * (ell k r S.z ρ + ell k r S.z (Matrix.of p.1.2))).re -
          (1 : ℝ) * (cStd * (ell k r S.z' (γ⁻¹ * ρ * γ) + ell k r S.z' (Matrix.of p.2.2))).re : ℝ) =
          (a - b) + ((1 : ℝ) * (cStd * ell k r S.z (Matrix.of p.1.2)).re -
            (1 : ℝ) * (cStd * ell k r S.z' (Matrix.of p.2.2)).re) := by
        simp only [a, b, mul_add, Complex.add_re]
        ring
      rw [hx, Complex.ofReal_add, mul_add, Complex.exp_add, Complex.ofReal_sub, mul_sub, Complex.exp_sub, hψ,
        div_self (Complex.exp_ne_zero _), one_mul]
    have hrh : B.rho S (C6.actR γ ρ p) F γ = B.rho S p F γ := by
      unfold B.rho B.sgs C6.actR
      simp only [Equiv.apply_symm_apply, hs]
    unfold D.orbIntegrand
    rw [hxi, hrh]
  have hX : Xi S w e x q = C6.actR γ (rhoX S γ w x) (Xi0 S w (Tx S γ w e x q)) := by
    apply Xi_eq <;> assumption
  obtain ⟨hρR, -⟩ : rhoX S γ w x ∈ C6.Rset γ ∧ C2.uMap k r S.z (rhoX S γ w x) = (lowS w x)ᴴ := by
    apply rhoX_spec <;> assumption
  have hρN := hρR.1
  have hρ'N := hρR.2
  have iρ : (rhoX S γ w x)⁻¹ * rhoX S γ w x = 1 := PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρN).1
  have iρ' : (γ⁻¹ * rhoX S γ w x * γ)⁻¹ * (γ⁻¹ * rhoX S γ w x * γ) = 1 :=
    PI.PolynomialProperness.GN.inv_mul ((WeylGroupFacts.nset_iff _).1 hρ'N).1
  have cρi := WeylGroupFacts.col_of_left_inv ((WeylGroupFacts.nset_iff _).1 hρN).2 iρ
  have cρi' := WeylGroupFacts.col_of_left_inv ((WeylGroupFacts.nset_iff _).1 hρ'N).2 iρ'
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩
  set P := Xi0 S w (Tx S γ w e x q) with hP
  have E1 : rhoX S γ w x * Matrix.of P.1.2 =
      C2.tauM k r S.z (G.upper (e (x, q.1.2.1))) * Matrix.of q.1.2.2 := by
    have := congrArg (fun s : B.SS k r => Matrix.of s.1.2) hX
    apply Matrix.ext
    intro i j
    simpa [Xi, C6.actR] using congrFun (congrFun this.symm i) j
  have E2 : (γ⁻¹ * rhoX S γ w x * γ) * Matrix.of P.2.2 =
      C2.tauM k r S.z' (G.upper q.2.2.1) * Matrix.of q.2.2.2 := by
    have := congrArg (fun s : B.SS k r => Matrix.of s.2.2) hX
    apply Matrix.ext
    intro i j
    simpa [Xi, C6.actR] using congrFun (congrFun this.symm i) j
  have c1 : WeylGroupFacts.col k r (Matrix.of P.1.2) := by
    have h : Matrix.of P.1.2 = (rhoX S γ w x)⁻¹ * (rhoX S γ w x * Matrix.of P.1.2) := by
      rw [← Matrix.mul_assoc, iρ, Matrix.one_mul]
    rw [h, E1]
    exact WeylGroupFacts.col_mul cρi (WeylGroupFacts.col_mul ((WeylGroupFacts.nset_iff _).1 (A.tau_N hz (HC.upper_mem _))).2
      ((WeylGroupFacts.nset_iff _).1 hq1).2)
  have c2 : WeylGroupFacts.col k r (Matrix.of P.2.2) := by
    have h : Matrix.of P.2.2 = (γ⁻¹ * rhoX S γ w x * γ)⁻¹ * ((γ⁻¹ * rhoX S γ w x * γ) * Matrix.of P.2.2) := by
      rw [← Matrix.mul_assoc, iρ', Matrix.one_mul]
    rw [h, E2]
    exact WeylGroupFacts.col_mul cρi' (WeylGroupFacts.col_mul ((WeylGroupFacts.nset_iff _).1 (A.tau_N hz' (HC.upper_mem _))).2
      ((WeylGroupFacts.nset_iff _).1 hq2).2)
  rw [hX]
  show θ (C6.actR γ (rhoX S γ w x) P) • D.orbIntegrand S γ F (C6.actR γ (rhoX S γ w x) P) =
    θ (C6.actR γ (rhoX S γ w x) P) • D.orbIntegrand S γ F P
  rw [key hρR P c1 c2]

include hγ hd hZw hpos hrel hemp he hμ0 hμ0' in
theorem orb_int [CompleteSpace Wp] {c1 c2 : NNReal} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hN1 : S.μN = c1 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0).map
      (fun p => Matrix.of.symm (C2.tauM k r S.z (G.upper p.1) * Matrix.of p.2)))
    (hN2 : S.μN = c2 • ((volume : Measure (G.UT (r + 1) → ℂ)).prod μ0').map
      (fun p => Matrix.of.symm (C2.tauM k r S.z' (G.upper p.1) * Matrix.of p.2)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (θ : B.SS k r → ℝ) (hθ : D.IsNormCut S γ (D.muR S γ w) θ)
    (hint : Integrable (fun p => θ p • D.orbIntegrand S γ F p) S.μSS) :
    Integrable (fun q => D.orbIntegrand S γ F (Xi0 S w q)) (nuR S w μ0 μ0') ∧
      ∫ p, θ p • D.orbIntegrand S γ F p ∂S.μSS =
        ((c1 * c2 : NNReal) : ℝ) • ∫ q, D.orbIntegrand S γ F (Xi0 S w q) ∂(nuR S w μ0 μ0') := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t7 : SFinite (nuR S w μ0 μ0') := by unfold nuR; infer_instance
  have hz : C2.StdZ k r S.z := ⟨S.z_mem, S.T_pos⟩
  have hz' : C2.StdZ k r S.z' := ⟨S.z'_mem, S.T'_pos⟩

  have nmul : ∀ a b : B.Mat k r, a ∈ Nset k r → b ∈ Nset k r → a * b ∈ Nset k r := by
    intro a b ha hb
    rw [WeylGroupFacts.nset_iff] at ha hb ⊢
    refine ⟨?_, WeylGroupFacts.col_mul ha.2 hb.2⟩
    have h1 : aᴴ * Hpk k r * a = Hpk k r := ha.1
    have h2 : bᴴ * Hpk k r * b = Hpk k r := hb.1
    show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
    rw [Matrix.conjTranspose_mul]
    calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
      _ = Hpk k r := by rw [h1, h2]
  have hrho : ∀ x : C2.Lstidx w → ℂ,
      D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x)) = rhoX S γ w x := fun x => rfl

  have hSS := ME.muSS_eq S w e hemp μ0 μ0' hμ0 hμ0' c1 c2 hN1 hN2
  have hc : ((c1 * c2 : NNReal) : ENNReal) ≠ 0 := by
    rw [ENNReal.coe_ne_zero]
    exact mul_ne_zero hc1.ne' hc2.ne'
  rw [hSS, nn_smul] at hint
  rw [hSS, nn_smul]
  have hint1 := (integrable_smul_measure hc ENNReal.coe_ne_top).1 hint
  have hXm : AEMeasurable (fun p : (C2.Lstidx w → ℂ) × RR k r w => Xi S w e p.1 p.2)
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := (meas_Xi S w e).aemeasurable
  have hint2 := (integrable_map_measure hint1.aestronglyMeasurable hXm).1 hint1
  have hgood : ∀ᵐ p ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')),
      θ (Xi S w e p.1 p.2) • D.orbIntegrand S γ F (Xi S w e p.1 p.2) = Hf S γ w θ F (Tt S γ w e p) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (C2.Lstidx w → ℂ)))
      (ν := nuR S w μ0 μ0')).ae
      (p := fun q : RR k r w => Matrix.of q.1.1 ∈ UWset k r S.z ∧ Matrix.of q.1.2.2 ∈ C2.N0set k r S.z ∧
        Matrix.of q.2.1 ∈ UWset k r S.z' ∧ Matrix.of q.2.2.2 ∈ C2.N0set k r S.z') (ae_good S w hμ0 hμ0')
    filter_upwards [h] with p hp
    exact comp_eq S hγ hd hZw hpos hrel e he θ F p.1 p.2 hp.2.1.1 hp.2.2.2.1
  have hint3 : Integrable (fun p => Hf S γ w θ F (Tt S γ w e p))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := hint2.congr hgood
  have hmp : MeasurePreserving (Tt S γ w e) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0'))
      ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
    apply OF.mp_Tt <;> assumption
  have hemb : MeasurableEmbedding (Tt S γ w e) := by
    apply OF.emb_Tt <;> assumption
  have hint4 : Integrable (Hf S γ w θ F) ((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) :=
    (hmp.integrable_comp_emb hemb).1 hint3
  have hI1 : ∫ p, θ (Xi S w e p.1 p.2) • D.orbIntegrand S γ F (Xi S w e p.1 p.2)
        ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) =
      ∫ p, Hf S γ w θ F p ∂((volume : Measure (C2.Lstidx w → ℂ)).prod (nuR S w μ0 μ0')) := by
    rw [integral_congr_ae hgood]
    exact hmp.integral_comp hemb _

  have hcut : ∀ P : B.SS k r, S.inSS P →
      ∫ x, θ (C6.actR γ (rhoX S γ w x) P) ∂(volume : Measure (C2.Lstidx w → ℂ)) = 1 := by
    intro P hP
    have h1 := hθ.2.2 P hP
    have hφ : Measurable fun x : C2.Lstidx w → ℂ =>
        (Matrix.of.symm (D.rhoOfU S γ (Matrix.conjTranspose (C2.lowOf (fun q => q.1) x))) : Mt k r) := by
      simp only [hrho]
      have hm : MeasM fun t : C2.Lstidx w → ℂ => rhoX S γ w (id t) := by
        apply OF.measM_rhoX <;> first | exact measurable_id | assumption
      exact hm
    unfold D.muR at h1
    rw [integral_map (f := fun y : Mt k r => θ (C6.actR γ (Matrix.of y) P)) hφ.aemeasurable
      (hθ.1.comp (meas_actR γ P)).aestronglyMeasurable] at h1
    simpa only [hrho, Equiv.apply_symm_apply] using h1
  have hSSae : ∀ᵐ q ∂(nuR S w μ0 μ0'), S.inSS (Xi0 S w q) := by
    filter_upwards [ae_good S w hμ0 hμ0'] with q hq
    refine ⟨hq.1, ?_, hq.2.2.1, ?_⟩
    · exact nmul _ _ (A.tau_N hz (lowPH_UT _)) hq.2.1.1
    · exact nmul _ _ (A.tau_N hz' (HC.upper_mem _)) hq.2.2.2.1
  have hfib : ∀ᵐ q ∂(nuR S w μ0 μ0'),
      ∫ x, Hf S γ w θ F (x, q) ∂(volume : Measure (C2.Lstidx w → ℂ)) = D.orbIntegrand S γ F (Xi0 S w q) := by
    filter_upwards [hSSae] with q hq
    show ∫ x, θ (C6.actR γ (rhoX S γ w x) (Xi0 S w q)) • D.orbIntegrand S γ F (Xi0 S w q)
      ∂(volume : Measure (C2.Lstidx w → ℂ)) = D.orbIntegrand S γ F (Xi0 S w q)
    rw [integral_smul_const, hcut _ hq, one_smul]
  refine ⟨?_, ?_⟩
  · exact hint4.integral_prod_right.congr hfib
  · rw [integral_smul_measure, integral_map hXm hint1.aestronglyMeasurable, hI1, integral_prod_symm _ hint4,
      integral_congr_ae hfib, ENNReal.coe_toReal]

end main

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OG
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.RearrApply
namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

section gen

variable {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

def inE : α × (β × γ) ≃ᵐ β × (α × γ) :=
  MeasurableEquiv.prodAssoc.symm.trans
    ((MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)).trans MeasurableEquiv.prodAssoc)

theorem inE_mp (μa : Measure α) (μb : Measure β) (μc : Measure γ) [SFinite μa] [SFinite μb] [SFinite μc] :
    MeasurePreserving (inE : α × (β × γ) ≃ᵐ β × (α × γ)) (μa.prod (μb.prod μc)) (μb.prod (μa.prod μc)) := by
  have e1 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μb μc)
  have e2 := (Measure.measurePreserving_swap (μ := μa) (ν := μb)).prod (MeasurePreserving.id μc)
  have e3 := measurePreserving_prodAssoc μb μa μc
  exact e3.comp (e2.comp e1)

end gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def rearr (k r : ℕ) (w : Equiv.Perm (Fin (r + 1))) :
    OD.RR k r w ≃ᵐ ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r :=
  (MeasurableEquiv.prodCongr inE inE).trans Dx2.SL.swap4

@[simp] theorem rearr_apply (w : Equiv.Perm (Fin (r + 1))) (q : OD.RR k r w) :
    rearr k r w q = ((q.1.2.1, q.2.2.1), ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2))) := rfl

private theorem measurePreserving_swap4 {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    [MeasurableSpace δ] (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ) [SFinite μa]
    [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (Dx2.SL.swap4 : (α × β) × γ × δ ≃ᵐ (α × γ) × β × δ) ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μb μc μd)
  have e3 := (Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd)
  have e4 := measurePreserving_prodAssoc μc μb μd
  have e5 := MeasurePreserving.symm _ (measurePreserving_prodAssoc μa μc (μb.prod μd))
  have h := (e5.comp ((MeasurePreserving.id μa).prod (e4.comp (e3.comp e2)))).comp e1
  convert h using 1
  funext p
  rfl

theorem mp_rearr (S : B.RealPlaceData k r Wp Wq) (w : Equiv.Perm (Fin (r + 1))) {μ0 μ0' : Measure (Mt k r)}
    (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0) (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') :
    MeasurePreserving (rearr k r w) (OD.nuR S w μ0 μ0')
      (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
        ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) := by
  haveI : IsFiniteMeasureOnCompacts S.μW := ⟨fun K hK => S.haarW.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts S.μW' := ⟨fun K hK => S.haarW'.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0 := ⟨fun K hK => hμ0.finite_compact K hK⟩
  haveI : IsFiniteMeasureOnCompacts μ0' := ⟨fun K hK => hμ0'.finite_compact K hK⟩
  haveI t1 : SFinite S.μW := inferInstance
  haveI t2 : SFinite μ0 := inferInstance
  haveI t5 : SFinite S.μW' := inferInstance
  haveI t6 : SFinite μ0' := inferInstance
  haveI t3 : SFinite (volume : Measure (C2.LPidx w → ℂ)) := inferInstance
  haveI t4 : SFinite (volume : Measure (G.UT (r + 1) → ℂ)) := inferInstance
  have h1 := (inE_mp S.μW (volume : Measure (C2.LPidx w → ℂ)) μ0).prod
    (inE_mp S.μW' (volume : Measure (G.UT (r + 1) → ℂ)) μ0')
  have h2 := measurePreserving_swap4 (volume : Measure (C2.LPidx w → ℂ)) (S.μW.prod μ0)
    (volume : Measure (G.UT (r + 1) → ℂ)) (S.μW'.prod μ0')
  exact h2.comp h1

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.RE
end

namespace Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.StabilizerDisintegration.OD
open scoped ComplexConjugate

noncomputable section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

private theorem herm_hpk_bvec_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  have ha := a.isLt
  have he : (eI k r a).val = a.val := rfl
  have hs : (esI k r a).val = 2 * r + k - a.val := rfl
  unfold herm bvec
  rw [← Pi.single_star, star_one, single_dotProduct, one_mul, Matrix.mulVec, dotProduct,
    Finset.sum_eq_single (eI k r a)]
  · have h1 : Hpk k r (esI k r a) (eI k r a) = 1 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_pos ⟨by omega, by omega⟩]
    rw [h1, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ a.val := fun h => hj (Fin.ext (h.trans he.symm))
    have h0 : Hpk k r (esI k r a) j = 0 := by
      simp only [Hpk]
      rw [if_neg (fun h => absurd h.1 (by omega)), if_neg (fun h => hj' (by have := h.2; omega)),
        if_neg (fun h => absurd h.2.1 (by omega))]
    rw [h0, zero_mul]
  · simp

theorem ell_eq (z : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : ell k r z g = C2.simpleUp (C2.uMap k r z g) := by
  unfold ell C2.simpleUp
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero, Fin.val_castSucc]
  refine Finset.sum_congr rfl fun a _ => ?_
  have ha : a.val + 1 < r + 1 := by omega
  rw [dite_eq_left ha]
  simp only [C2.uMap, Fin.val_castSucc, a.isLt, dite_true]
  rw [herm_hpk_bvec_esI]
  simp only [fvec]
  by_cases h1 : a.val + 1 < r
  · simp [h1, bvec, Matrix.mulVec_single]
  · simp [h1]

theorem psi_prod (a b : ℂ) :
    Complex.exp (Complex.I * (((1 : ℝ) * (cStd * a).re - (1 : ℝ) * (cStd * b).re : ℝ) : ℂ)) =
      C2.psiC cStd a * star (C2.psiC cStd b) := by
  simp only [C2.psiC, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

theorem xi_at (S : B.RealPlaceData k r Wp Wq) {v u' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hv : v ∈ C2.UTset (r + 1))
    (hu' : u' ∈ C2.UTset (r + 1)) {n0 n0' : Mt k r} (hn0 : Matrix.of n0 ∈ C2.N0set k r S.z)
    (hn0' : Matrix.of n0' ∈ C2.N0set k r S.z') (h h' : Mt k r) :
    B.xiTau S (1, 1) ((h, Matrix.of.symm (C2.tauM k r S.z v * Matrix.of n0)),
      (h', Matrix.of.symm (C2.tauM k r S.z' u' * Matrix.of n0'))) =
      C2.psiC cStd (C2.simpleUp v) * star (C2.psiC cStd (C2.simpleUp u')) := by
  have key : ∀ {z : Fin (2 * r + k + 1) → ℂ}, C2.StdZ k r z → ∀ {v : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ},
      v ∈ C2.UTset (r + 1) → ∀ {n0 : Mt k r}, Matrix.of n0 ∈ C2.N0set k r z →
      ell k r z (C2.tauM k r z v * Matrix.of n0) = C2.simpleUp v := by
    intro z hz v hv n0 hn0
    rw [ell_eq, HC.uMap_mul hz (HC.tau_N hz hv) hn0.1, HC.tau_u hz hv, hn0.2, mul_one]
  unfold B.xiTau B.lam
  simp only [Equiv.apply_symm_apply]
  rw [key ⟨S.z_mem, S.T_pos⟩ hv hn0, key ⟨S.z'_mem, S.T'_pos⟩ hu' hn0']
  exact psi_prod _ _

theorem pt_eq (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) (p : B.SS k r)
    (hp1 : Matrix.of p.1.2 ∈ C2.N0set k r S.z) (hp2 : Matrix.of p.2.2 ∈ C2.N0set k r S.z') :
    D.orbIntegrand S γ F (Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2)))) =
      (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
        B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have hv := OD.lowPH_UT Y.1
  have hu := HC.upper_mem Y.2
  have hr : B.rho S ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) F γ =
      B.rho S p F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
    unfold B.rho B.sgs
    simp only [Equiv.apply_symm_apply, Matrix.mul_inv_rev, Matrix.mul_assoc]
  unfold D.orbIntegrand
  rw [show Xi0 S w ((p.1.1, (Y.1, p.1.2)), (p.2.1, (Y.2, p.2.2))) =
      ((p.1.1, Matrix.of.symm (C2.tauM k r S.z (lowP w Y.1)ᴴ * Matrix.of p.1.2)),
        (p.2.1, Matrix.of.symm (C2.tauM k r S.z' (G.upper Y.2) * Matrix.of p.2.2))) from rfl,
    xi_at S hv hu hp1 hp2 p.1.1 p.2.1, hr]

theorem cell_int [CompleteSpace Wp] (S : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r) (w : Equiv.Perm (Fin (r + 1)))
    {μ0 μ0' : Measure (Mt k r)} (hμ0 : B.IsHaarOn (C2.N0set k r S.z) μ0)
    (hμ0' : B.IsHaarOn (C2.N0set k r S.z') μ0') (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hI : Integrable (fun q => D.orbIntegrand S γ F (Xi0 S w q)) (nuR S w μ0 μ0')) :
    ∫ q, D.orbIntegrand S γ F (Xi0 S w q) ∂(nuR S w μ0 μ0') =
      ∫ Y : (C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ),
        (C2.psiC cStd (C2.simpleUp (lowP w Y.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper Y.2)))) •
          PBI.fibInt S μ0 μ0' F ((C2.tauM k r S.z (lowP w Y.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper Y.2)) := by
  have := Dx2.OrbJ.sigmaF hμ0
  have := Dx2.OrbJ.sigmaF hμ0'
  have := Dx2.OrbJ.sigmaF S.haarW
  have := Dx2.OrbJ.sigmaF S.haarW'
  have hmp := RE.mp_rearr S w hμ0 hμ0'
  let Φ : ((C2.LPidx w → ℂ) × (G.UT (r + 1) → ℂ)) × B.SS k r → (Wq →L[ℂ] Wp) := fun x =>
    (C2.psiC cStd (C2.simpleUp (lowP w x.1.1)ᴴ) * star (C2.psiC cStd (C2.simpleUp (G.upper x.1.2)))) •
      B.rho S x.2 F ((C2.tauM k r S.z (lowP w x.1.1)ᴴ)⁻¹ * γ * C2.tauM k r S.z' (G.upper x.1.2))
  have hae : (fun q => D.orbIntegrand S γ F (Xi0 S w q)) =ᵐ[nuR S w μ0 μ0'] fun q => Φ (RE.rearr k r w q) := by
    filter_upwards [OG.ae_good S w hμ0 hμ0'] with q hq
    rw [RE.rearr_apply]
    exact pt_eq S γ w F (q.1.2.1, q.2.2.1) ((q.1.1, q.1.2.2), (q.2.1, q.2.2.2)) hq.2.1 hq.2.2.2
  have hIp : Integrable Φ (((volume : Measure (C2.LPidx w → ℂ)).prod (volume : Measure (G.UT (r + 1) → ℂ))).prod
      ((S.μW.prod μ0).prod (S.μW'.prod μ0'))) :=
    (hmp.integrable_comp_emb (RE.rearr k r w).measurableEmbedding).mp (hI.congr hae)
  rw [integral_congr_ae hae, hmp.integral_comp' Φ, integral_prod Φ hIp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
  simp only [Φ]
  rw [integral_smul]
  rfl

end

end Formalism.FourierDecayAlt.P.StabilizerDisintegration.OJ
