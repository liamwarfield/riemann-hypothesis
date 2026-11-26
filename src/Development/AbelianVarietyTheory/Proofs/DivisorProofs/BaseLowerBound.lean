module

public import Formalism.LocalToGlobal.GroupLattices.JointServices.VwResChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeLowerBlockVectorMultipleKernelTranslate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeries
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeries
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BaseCmp
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem unitOff_inv_mul' {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v)⁻¹ := by
  obtain ⟨hu0, n, hn1, hn2⟩ := hu
  obtain ⟨hv0, m, hm1, hm2⟩ := hv
  refine ⟨inv_ne_zero (mul_ne_zero hu0 hv0), n + m, ?_, ?_⟩
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹ = ((N : ℂ) ^ n * u⁻¹) * ((N : ℂ) ^ m * v⁻¹) := by
      rw [pow_add, mul_inv]; ring
    rw [e]; exact hn2.mul hm2
  · have e : (N : ℂ) ^ (n + m) * (u * v)⁻¹⁻¹ = ((N : ℂ) ^ n * u) * ((N : ℂ) ^ m * v) := by
      rw [inv_inv, pow_add]; ring
    rw [e]; exact hn1.mul hm1

theorem exists_unif' (E : Type) [Field E] [NumberField E] (Q : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) :
    ∃ ϖ : 𝓞 E, ϖ ≠ 0 ∧ ∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2 := by
  have hx : ∀ PP : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ∃ x ∈ PP.asIdeal, x ∉ PP.asIdeal ^ 2 := fun PP => by
    simpa using Ideal.exists_mem_pow_notMem_pow_succ PP.asIdeal PP.ne_bot PP.isPrime.ne_top 1
  choose x hx1 hx2 using hx
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Q)
    (fun PP => PP.asIdeal) (fun _ => 2) (fun PP _ => Ideal.prime_of_isPrime PP.ne_bot PP.isPrime)
    (fun PP _ PP' _ h e => h (IsDedekindDomain.HeightOneSpectrum.ext e)) (fun PP => x PP.1)
  have key : ∀ PP ∈ Q, y ∈ PP.asIdeal ∧ y ∉ PP.asIdeal ^ 2 := fun PP hPP => by
    have h1 := hy PP hPP
    have hle : PP.asIdeal ^ 2 ≤ PP.asIdeal := Ideal.pow_le_self (by norm_num)
    refine ⟨?_, fun h => hx2 PP ?_⟩
    · have := PP.asIdeal.add_mem (hle h1) (hx1 PP)
      simpa using this
    · have := (PP.asIdeal ^ 2).sub_mem h h1
      simpa using this
  by_cases hQ : Q.Nonempty
  · obtain ⟨PP, hPP⟩ := hQ
    refine ⟨y, fun h0 => (key PP hPP).2 (h0 ▸ Ideal.zero_mem _), key⟩
  · refine ⟨1, one_ne_zero, fun PP hPP => absurd ⟨PP, hPP⟩ hQ⟩

theorem flatKer_holds : FlatKer := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV B hBg hB ξ ξR ω φ hK hQt N hN hNQ
  obtain ⟨eg, eQ, fg, heg, heQ, hfg, hflat⟩ := GlobalTheory.BaseCmp.flatTwoStep_holds D G Pl0 T0 A Ks R F hC i ξ B.de.chi ξR ω φ B hBg hB hK hK.chr
  obtain ⟨ϖ, hϖ0, hϖ⟩ := exists_unif' D.host.E B.de.Q
  have hϖE : (ϖ : D.host.E) ≠ 0 := by exact_mod_cast hϖ0
  obtain ⟨z, hz, hzm⟩ := GlobalTheory.CentScal.exists_isCentAt_scalar D i B.de.Q eQ heQ (ϖ : D.host.E) hϖE
  obtain ⟨κ, hκ, hact⟩ := GlobalTheory.T.central_uniformiser_acts_by_dilation_tame_kernel D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖE hϖ z hzm
  obtain ⟨Gc, hG, hSB, hφ⟩ := GlobalTheory.T.tameKernel_vector_unit_mul_dilated_flat D G Pl0 T0 A Ks R F hC hQG i hV ξ B.de.chi ξR B.de.Q ω φ hK hQt N hN hNQ
    eg eQ fg heg heQ hfg ϖ hϖ0 hϖ
  obtain ⟨Tm, hTm⟩ := hflat.1
  have hvT := hflat.2 Tm hTm
  have hφT := hφ Tm hTm
  have hne : κ * Gc ≠ 0 := mul_ne_zero hκ.1 hG.1
  have hcomp : ∀ x : WO (Vc D i) (Wc D i), dil i (ϖ : D.host.E) (dil i (ϖ : D.host.E)⁻¹ x) = x := by
    intro x
    show Matrix.map (Matrix.map x fun w => incA D ((ϖ : D.host.E)⁻¹) * w) (fun w => incA D (ϖ : D.host.E) * w) = x
    ext a b
    simp only [Matrix.map_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hϖE, map_one, one_mul]
  have hvec : (princ B).vecBase = (κ * Gc)⁻¹ • ω (z, 1) φ := by
    rw [hφT, hact Tm hTm _ hSB]
    simp only [hcomp]
    have hsm : (fun x : WO (Vc D i) (Wc D i) => Gc * flatDat R i B.de.Q ξR eQ x) = Gc • flatDat R i B.de.Q ξR eQ := rfl
    rw [hsm, map_smul, ← hvT, smul_smul, smul_smul, mul_assoc (κ * Gc)⁻¹, inv_mul_cancel₀ hne, one_smul]
  refine ⟨z, (κ * Gc)⁻¹, hz, unitOff_inv_mul' hκ hG, fun h P => ?_⟩
  have hθ : IsInfFam R.θ := hK.vec.1.2.inf
  have hth := GlobalTheory.VecTheta.isThetaFunO_thPVec hK.vec
  funext g
  rw [hvec, Pi.smul_apply, series_apply, series_apply, hB.fock_eq, hB.fock_eq, GlobalTheory.FiniteFock.pureTensorO_smul,
    ← GlobalTheory.OrientedHeis.om_fin_pureTensorO R.ψ _ _ _ _ ω hK.weil R.θ hθ z hz.2.1 1 (one_mem _) _ _ _ _ φ _ hth,
    map_smul, Pi.smul_apply, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

end GlobalTheory.BigOn.Exp.SerBase
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeriesStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatDatum_series_unit_times_kernel_series : FlatKer := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | exact GlobalTheory.BigOn.Exp.SerBase.flatKer_holds | (intros; apply GlobalTheory.BigOn.Exp.SerBase.flatKer_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePow
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase GlobalTheory.OnCmp GlobalTheory.RealIndexBound GlobalTheory.ConjTwist
open GlobalTheory.OnTies
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CentralLattice

open GlobalTheory.FreeBlockTwist

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem inCoefLat_pow' (R : RealDat D A Ks) (i : Fin D.R.m) {β : GL (Fin (Vc D i).rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} (hβ : IsSDFrame (Vc D i) β Λ 1) {a : AE D}
    {k : GA D (Vc D i)} (hk : Formalism.L2.Theta.SuppAt a (Vc D i) k) {p : ℕ}
    (ha : ∀ PP : Pl D.host.E, (p : 𝓞 D.host.E) ∉ PP.asIdeal →
      GlobalTheory.StdFrames.cpt PP (toEAf D (a + cA D a)) = 0) :
    ∃ m : ℕ, ∀ l, m ≤ l → ∀ h w, InCoefLat R i h w → InCoefLat R i (h * k) (((p : ℂ) ^ l) • w) := by
  obtain ⟨m₁, h₁⟩ := exists_pow_hat hβ.choose_spec.1 hk ha
  obtain ⟨m₂, h₂⟩ := exists_pow_hat hβ.choose_spec.1 (GlobalTheory.SplitLinear.suppAt_inv hk) ha
  refine ⟨(m₁ + m₂) * GlobalTheory.NabScale.scaleExp (Formalism.IndefR.FWT.lamV D i), fun l hl h w hw => ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hl
  obtain ⟨gramR, c0R, c0L, hT, P, hP, rfl⟩ := hw
  refine ⟨gramR, c0R, c0L, hT, ?_⟩
  have e1 := smul_mem_hLat hβ (h₂ (m₁ + m₂) (Nat.le_add_left _ _)) h
  have e2 := smul_mem_hLat hβ (k := k⁻¹) (by rw [inv_inv]; exact h₁ (m₁ + m₂) (Nat.le_add_right _ _)) (h * k)
  rw [mul_inv_cancel_right] at e2
  have e3 := Submodule.smul_mem _ ((p ^ d : ℕ) : 𝓞 D.what₂.LL)
    (nabAtr_scale (labLL D) (Formalism.IndefR.FWT.lamV D i) _ (by first | exact GlobalTheory.RepsCompare.isLattice_hLat _ _ | exact hLat_full _ _) e1 e2 P hP)
  refine ⟨_, e3, ?_⟩
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, map_smulₛₗ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  rw [map_pow, map_natCast]
  push_cast
  ring

theorem centLat : CentLat := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R i Q z hz N hN hQ
  obtain ⟨-, -, e, he, hsupp⟩ := hz
  obtain ⟨β, Λ, hβ⟩ := GlobalTheory.AdIsomObj.frames_exist D (Vc D i) 1
  have ha : ∀ PP : Pl D.host.E, (N : 𝓞 D.host.E) ∉ PP.asIdeal →
      GlobalTheory.StdFrames.cpt PP (toEAf D (e + cA D e)) = 0 := fun PP hPP => by
    rw [RingHom.map_add (f := _), RingHom.map_add (f := _), (cpt_sum he PP).2 fun h => hPP (hQ PP h), zero_add, GlobalTheory.StdFrames.toEAf_cA]
    exact GlobalTheory.StdFrames.cpt_sg_eq_zero ((cpt_sum he _).2 fun h => hPP ((GlobalTheory.StdFrames.natCast_mem_cP PP N).1 (hQ _ h)))
  obtain ⟨m₁, h₁⟩ := inCoefLat_pow' R i hβ hsupp ha
  obtain ⟨m₂, h₂⟩ := inCoefLat_pow' R i hβ (GlobalTheory.SplitLinear.suppAt_inv hsupp) ha
  refine ⟨max m₁ m₂, fun h _ y => ⟨fun hy => h₁ (max m₁ m₂) (le_max_left m₁ m₂) h y hy, fun hy => ?_⟩⟩
  have := h₂ (max m₁ m₂) (le_max_right m₁ m₂) (h * z) y hy
  rwa [mul_inv_cancel_right] at this

end GlobalTheory.CentralLattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePowStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow : CentLat := by
  first | exact @GlobalTheory.CentralLattice.centLat | exact GlobalTheory.CentralLattice.centLat | (intros; apply GlobalTheory.CentralLattice.centLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypes
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open GlobalTheory.BigTop GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

namespace GlobalTheory.TraceRatPf

theorem zero_of_span' {ι : Type} [Fintype ι] [DecidableEq ι] {L : ι → Type} [∀ j, AddCommGroup (L j)] [∀ j, Module ℂ (L j)]
    {X : Type} [AddCommGroup X] [Module ℂ X] (F : (∀ j, L j) →ₘₗ[ℂ] X) (v₀ : ∀ j, L j) (P : ∀ j, L j → Prop)
    (hspan : ∀ j, Submodule.span ℂ {u | P j u} = ⊤)
    (hstep : ∀ (v : ∀ j, L j) (j : ι) (u : L j), v j = v₀ j → P j u → F v = 0 → F (Function.update v j u) = 0)
    (h0 : F v₀ = 0) : ∀ v, F v = 0 := by
  have key : ∀ s : Finset ι, ∀ v : ∀ j, L j, (∀ j ∉ s, v j = v₀ j) → F v = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      have : v = v₀ := funext fun j => hv j (Finset.notMem_empty j)
      rw [this]; exact h0
    | insert a s ha ih =>
      intro v hv
      have h1 : F (Function.update v a (v₀ a)) = 0 := ih _ fun j hj => by
        by_cases hja : j = a
        · subst hja; simp
        · rw [Function.update_of_ne hja]; exact hv j (by simp [hja, hj])
      have hmem : v a ∈ Submodule.span ℂ {u | P a u} := by rw [hspan a]; trivial
      have hall : ∀ u ∈ Submodule.span ℂ {u | P a u},
          F (Function.update (Function.update v a (v₀ a)) a u) = 0 := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu => exact hstep _ a u (by simp) hu h1
        | zero => exact F.map_update_zero _ _
        | add x y _ _ hx hy => rw [F.map_update_add, hx, hy, add_zero]
        | smul c x _ hx => rw [F.map_update_smul, hx, smul_zero]
      have e : Function.update (Function.update v a (v₀ a)) a (v a) = v := by simp
      rw [← e]; exact hall _ hmem
  exact fun v => key Finset.univ v (fun j hj => absurd (Finset.mem_univ j) hj)

theorem adForm_lowT_equiv' {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hHW : R.models_HW) (i : Fin D.R.m) (x : Fin (R.nW i) → D.what₂.LL) (τ : D.what₂.Tau) (k : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (hk : k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε τ)) (v : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (u : lowT (R.MW i (sg0 D A)) τ) (hu : ((u : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ) = (R.MW i (sg0 D A)).σ τ k ((v τ : (R.MW i (sg0 D A)).sm τ) : (R.MW i (sg0 D A)).H τ)) : adForm R i x (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) = Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ)) (adForm R i x (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) := by
  have hmem : adForm R i x ∈ R.Wall i (sg0 D A) := by
    rw [← (hHW i (sg0 D A)).2.1]
    exact LinearMap.mem_range_self _ _
  have hfr : IsUnit ((R.MW i (sg0 D A)).fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 ((R.MW i (sg0 D A)).fr_unit τ)
  have e1 : (R.MW i (sg0 D A)).fr τ * ((R.MW i (sg0 D A)).fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hfr
  have hkJ : kᴴ * Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) * k = Formalism.REAL.Jm ((R.MW i (sg0 D A)).ε τ) := by
    have hu1 : kᴴ * k = 1 := (Matrix.mem_unitaryGroup_iff').1 hk.1
    rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  have hg : ((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) τ) := by
    show _ = _
    rw [← (R.MW i (sg0 D A)).fr_gram τ]
    have e3 : (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ * ((R.MW i (sg0 D A)).fr τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((R.MW i (sg0 D A)).fr τ)⁻¹)ᴴ, e3, Matrix.one_mul,
      ← Matrix.mul_assoc ((R.MW i (sg0 D A)).fr τ) (((R.MW i (sg0 D A)).fr τ)⁻¹), e1, Matrix.one_mul]
    rw [← Matrix.mul_assoc kᴴ, ← Matrix.mul_assoc (kᴴ * _), hkJ]
  have hrep : (R.MW i (sg0 D A)).rep τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ) =
      (R.MW i (sg0 D A)).σ τ k := by
    unfold Formalism.IndefR.Mult.DSModel.rep
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, e1, Matrix.one_mul, Matrix.mul_assoc, e1, Matrix.mul_one]
  have hupd : (fun ρ => (Function.update v τ u ρ : (R.MW i (sg0 D A)).sm ρ)) =
      Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ) := by
    funext ρ
    by_cases hρ : ρ = τ
    · subst hρ; simp
    · simp [Function.update_of_ne hρ]
  rw [hupd]
  suffices H : ∀ T ∈ R.Wall i (sg0 D A), T (Function.update (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ)) τ (u : (R.MW i (sg0 D A)).sm τ)) =
      Formalism.L2.Theta.rTr (Wc D i) (atTau R.θ (Wc D i) τ (((R.MW i (sg0 D A)).fr τ)⁻¹ * k * (R.MW i (sg0 D A)).fr τ))
        (T (fun ρ => (v ρ : (R.MW i (sg0 D A)).sm ρ))) from H _ hmem
  intro T0 hT0
  induction hT0 using Submodule.span_induction with
  | mem T hT =>
    exact hT.equiv τ _ hg _ _ (by rw [hrep]; exact hu)
  | zero => rfl
  | add S T _ _ hS hT =>
    simp only [MultilinearMap.add_apply, hS, hT]
    rfl
  | smul a T _ hT =>
    simp only [MultilinearMap.smul_apply, hT]
    rfl

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem translate_all {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hcore : GlobalTheory.Hk3.Core R F) (hU : R.LUnif) (i : Fin D.R.m) (v₀ : (R.MW i (sg0 D A)).Vec)
    (hext : IsExtVec (R.MW i (sg0 D A)) v₀) {ξ χ ξR Q ω φ} (hker : KerDat R i ξ χ ξR Q ω φ)
    (h : GA D (Vc D i)) (y : (R.cV i).W) (u : ∀ τ, lowT (R.MW i (sg0 D A)) τ)
    (hu : ∀ τ, (u τ : (R.MW i (sg0 D A)).sm τ) = v₀ τ) (x : Fin (R.nW i) → D.what₂.LL)
    (hx : adForm R i x (fun τ => u τ) = singleSeries R i ω φ h y u) (g : G) :
    ∀ v : ∀ τ, lowT (R.MW i (sg0 D A)) τ, adForm R i ((R.FW i).ρ g x) (fun τ => v τ) =
      D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) •
        Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) (singleSeries R i ω φ h y v) := by
  have hs0 : sg0 D A = D.what₂.embLL := sgAt_mk _ R.hv0
  have hσ : GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature.OverK (sg0 D A) :=
    fun x _ => congrArg (fun s : D.what₂.LL →+* ℂ => s (D.embE x)) hs0
  have hc : (sg0 D A) (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) = D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) :=
    congrArg (fun s : D.what₂.LL →+* ℂ => s (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)) hs0
  let Lin : LowT (R.MW i (sg0 D A)) →ₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    { toFun := fun t g' => Datum.thetaKO ω h g' (Datum.pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
        (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) φ (R.ioP i t y))
      map_add' := fun a b => by funext g'; simp [Datum.thetaKO, map_add (f := _)]
      map_smul' := fun a b => by funext g'; simp [Datum.thetaKO, map_smul] }
  let act := Formalism.IndefR.Links.actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g)
  let c : ℂ := D.what₂.embLL (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL)
  let Rt : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (c • (act ∘ₗ Lin)).compMultilinearMap (PiTensorProduct.tprod ℂ)
  let Lf : (∀ ρ, lowT (R.MW i (sg0 D A)) ρ) →ₘₗ[ℂ] (GA D (Wc D i) → ℂ) :=
    (adForm R i ((R.FW i).ρ g x)).compLinearMap fun ρ => (lowT (R.MW i (sg0 D A)) ρ).subtype
  have hRt : ∀ w, Rt w = c • act (singleSeries R i ω φ h y w) := fun w => rfl
  have hLf : ∀ w, Lf w = adForm R i ((R.FW i).ρ g x) (fun ρ => (w ρ : (R.MW i (sg0 D A)).sm ρ)) := fun w => rfl
  have hrs : ∀ (g' : GA D (Wc D i)) (a b : GA D (Wc D i) → ℂ) (s : ℂ),
      Formalism.L2.Theta.rTr (Wc D i) g' a - s • Formalism.L2.Theta.rTr (Wc D i) g' b = Formalism.L2.Theta.rTr (Wc D i) g' (a - s • b) :=
    fun _ _ _ _ => rfl
  have hat : Lf u = Rt u := by
    rw [hLf, hRt]
    have e := congrArg (fun T => T (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) ((hU i (sg0 D A)).2.2 g x)
    change adForm R i ((R.FW i).ρ g x) _ = _ at e
    rw [e, hc]
    change c • act (adForm R i x (fun ρ => (u ρ : (R.MW i (sg0 D A)).sm ρ))) = _
    rw [hx]
  have key := zero_of_span' (Lf - Rt) u
    (fun ρ z => ∃ k ∈ Formalism.REAL.Kset ((R.MW i (sg0 D A)).ε ρ),
      ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((v₀ ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ))
    (fun ρ => GlobalTheory.LowSpan.span_translates_eq_top _ _ hext ρ
      ((GlobalTheory.HolLowOnce.lowSm_and_lowIrr D _ _ _ (GlobalTheory.GalLift.ProjLift.holShape_of_overK R i hσ)).2 ρ))
    (fun w ρ z hw ⟨k, hk, hu'⟩ h0 => by
      have hu2 : ((z : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) = (R.MW i (sg0 D A)).σ ρ k ((w ρ : (R.MW i (sg0 D A)).sm ρ) : (R.MW i (sg0 D A)).H ρ) := by
        rw [hu', hw, hu]
      have e1 := adForm_lowT_equiv' R hcore.models.HW i ((R.FW i).ρ g x) ρ k hk w z hu2
      have e2 := GlobalTheory.SeriesKEquiv.singleSeries_kEquiv R F hcore i _ χ ξR _ ω φ hker _ _ φ hker.vecOf h y g ρ k hk w z hu2
      rw [MultilinearMap.sub_apply, hLf, hRt, e1, e2]
      change Formalism.L2.Theta.rTr (Wc D i) _ (Lf w) - c • Formalism.L2.Theta.rTr (Wc D i) _ (act _) = 0
      rw [hrs, ← hRt, ← MultilinearMap.sub_apply, h0]
      rfl)
    (by rw [MultilinearMap.sub_apply, hat, sub_self])
  intro w
  have := key w
  rw [MultilinearMap.sub_apply, sub_eq_zero, hLf, hRt] at this
  exact this

end GlobalTheory.TraceRatPf

namespace GlobalTheory.TraceRatPf

theorem adForm_sum {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {ι : Type} (s : Finset ι) (f : ι → Fin (R.nW i) → D.what₂.LL) :
    adForm R i (∑ g ∈ s, f g) = ∑ g ∈ s, adForm R i (f g) := by
  induction s using Finset.induction_on with
  | empty =>
    have e := GlobalTheory.TraceClassRank.adForm_smul (R := R) (i := i) 0 0
    rw [zero_smul, map_zero, zero_smul] at e
    simpa using e
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, GlobalTheory.TraceClassRank.adForm_add, ih]

theorem traceRat : TraceRat := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hcore hU i v₀ hext ξ χ ξR Q ω φ hker U ψ h y u hu x hx
  let c' : G → D.what₂.LL := fun g =>
    if hg : g ∈ U then (((ψ ⟨g, hg⟩)⁻¹ * ((R.FW i).chi g)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) else 0
  refine ⟨∑ g, c' g • (R.FW i).ρ g x, fun v => ?_⟩
  rw [adForm_sum, MultilinearMap.sum_apply]
  unfold levelTrace gaL
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [GlobalTheory.TraceClassRank.adForm_smul, MultilinearMap.smul_apply,
    translate_all R F hcore hU i v₀ hext hker h y u hu x hx g v, LinearMap.smul_apply, smul_smul, ← map_mul]
  congr 2
  by_cases hg : g ∈ U
  · simp only [c', dif_pos hg]
    rw [← Units.val_mul, mul_assoc, inv_mul_cancel, mul_one]
  · simp only [c', dif_neg hg, zero_mul, map_zero]

end GlobalTheory.TraceRatPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypesStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes : TraceRat := by
  first | exact @GlobalTheory.TraceRatPf.traceRat | exact GlobalTheory.TraceRatPf.traceRat | (intros; apply GlobalTheory.TraceRatPf.traceRat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlace
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.BigOn.Exp.SerBase

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem natPrime_notMem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (hne : q ≠ Formalism.EigenvalueLevelCeiling.plc v) : (q : 𝓞 K) ∉ v.asIdeal := by
  intro hmem
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at hmem
  have hdvd : Formalism.EigenvalueLevelCeiling.plc v ∣ q := (ringChar.spec (𝓞 K ⧸ v.asIdeal) q).1 hmem
  exact hne ((Nat.prime_dvd_prime_iff_eq (Formalism.L2.DIV.plc_prime' v) hq).1 hdvd).symm

theorem ownAt_prime_ne (D : D7) (w : D.what₂.places.Pl) :
    (ownAt D (D.plEq w)).Prime ∧ ownAt D (D.plEq w) ≠ Formalism.EigenvalueLevelCeiling.plc (D.plEq w) := by
  unfold ownAt
  split_ifs with h
  · exact ⟨D.host.pde'_prime, fun e => D.host.pde_ne (h.symm.trans e.symm)⟩
  · exact ⟨D.host.pde_prime, fun e => h e.symm⟩

theorem ownUnit : OwnUnit := by
  intro D c w
  obtain ⟨hq, hne⟩ := ownAt_prime_ne D w
  set q := ownAt D (D.plEq w) with hqdef
  have hnot := natPrime_notMem (D.plEq w) hq hne
  have hv : (D.plEq w).valuation D.what₂.LL (q : D.what₂.LL) = 1 := by
    have := ((D.plEq w).valuation_eq_one_iff_notMem (K := D.what₂.LL)).2 hnot
    simpa using this
  have hq0 : (q : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hnn : (0 : WithTop ℤ) ≤ D.what₂.places.val w (q : D.what₂.LL)⁻¹ :=
    (D.val_nonneg_iff w _).2 (by rw [map_inv₀, hv, inv_one])
  obtain ⟨y, hy⟩ := (c.embW_w w _).1 hnn
  rw [map_inv₀, map_natCast] at hy
  have hqF : ((q : ℕ) : FractionRing (c.Oe w)) ≠ 0 := by
    have := (map_ne_zero (c.embW w)).2 hq0
    rwa [map_natCast] at this
  have h1 : algebraMap (c.Oe w) (FractionRing (c.Oe w)) (y * (q : c.Oe w)) = 1 := by
    rw [map_mul, hy, map_natCast]
    exact inv_mul_cancel₀ hqF
  have h2 : y * (q : c.Oe w) = 1 := by
    apply IsFractionRing.injective (c.Oe w) (FractionRing (c.Oe w))
    rw [h1, map_one]
  exact (Units.mkOfMulEqOne (q : c.Oe w) y (by rw [mul_comm]; exact h2)).isUnit

end GlobalTheory.BigOn.Exp.SerBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlaceStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ownPrime_isUnit_at_place : OwnUnit := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.ownUnit | exact GlobalTheory.BigOn.Exp.SerBase.ownUnit | (intros; apply GlobalTheory.BigOn.Exp.SerBase.ownUnit <;> assumption)
end
end

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem exists_of_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : FractionRing O →+* ℂ) {N : ℕ}
    (hN : IsUnit (N : O)) {b : FractionRing O} {k : ℕ} (h : IsIntegral ℤ ((N : ℂ) ^ k * e b)) :
    ∃ o : O, algebraMap O (FractionRing O) o = b := by
  have h1 : IsIntegral O ((N : FractionRing O) ^ k * b) := by
    obtain ⟨f, hf, h0⟩ := h
    refine ⟨f.map (Int.castRingHom O), hf.map _, e.injective ?_⟩
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero, map_mul, map_pow, map_natCast, ← h0]
    congr 1
    exact RingHom.ext_int _ _
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨u, hu⟩ := hN.pow k
  refine ⟨(u⁻¹ : Oˣ) * y, ?_⟩
  have e2 : algebraMap O (FractionRing O) (u⁻¹ : Oˣ) * (N : FractionRing O) ^ k = 1 := by
    rw [← map_natCast (algebraMap O (FractionRing O)), ← map_pow, ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, hy, ← mul_assoc, e2, one_mul]

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem tmul_mem_realBase (hL : Links2 p) (h1 : KerOf p w j) (h2 : TraceOf p w j) (h3 : KerRat p w j) (h4 : LatIo p w j)
    (h5 : ReadCmp p w j) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    {rd : Can p w j} (hfit : Fit p w j hρ ν) (hcan : IsCan p rd) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j))
    {Q : PolF D (Wc D j).rank (Vc D j).rank} (hQ : Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h)
    {g : D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w)}
    (hg : rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q) :
    ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd := by
  classical
  have hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hguard : QGuard (R2 p) := p.qGuard
  obtain ⟨hpin, e, he1, he2⟩ := hfit.adapted
  obtain ⟨hν, c, hsc, n, hn, hνc⟩ := hfit.norm
  rw [p.phsOne j, map_one, one_mul] at hνc
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hνc
    exact hν ((pow_eq_zero_iff hn).1 hνc)
  obtain ⟨hBo, hQ', ξR, φ, hk⟩ := h1 ρ hρ hpin
  obtain ⟨u, hu, hio⟩ := h4 ρ hρ hpin c hc hsc
  obtain ⟨y, hy, hyio⟩ := hio h hh Q hQ
  have hU := hO D ex.nch w
  have hN0 : ownAt D (D.plEq w) ≠ 0 := fun h0 => by
    rw [h0, Nat.cast_zero] at hU
    exact not_isUnit_zero hU
  have hNC : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hpl : ∀ PP ∈ plW p w, ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => (Finset.mem_filter.1 hPP).2
  obtain ⟨z, cA, hz, hcA, hser⟩ := hF D _ _ _ _ _ (R2 p) (F2 p) hcore hguard j (p.pins j).2.lift.std _ (hρ.base _ j _) hBo _ ξR _ φ
    (by rw [hQ']; exact hk) ⟨_, by rw [hQ']; exact Finset.filter_subset _ _⟩ _ hN0 (by rw [hQ']; exact hpl)
  obtain ⟨m, hm⟩ := hC D _ _ _ _ _ (R2 p) j _ z hz _ hN0 (by rw [hQ']; exact hpl)
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hz.2.1
  have hy' := (hm h hh y).1 hy
  obtain ⟨x, hx⟩ := h3 _ _ _ _ hk (h * z) hhz _ hy' u hu
  obtain ⟨x', hx'⟩ := hTr D _ _ _ _ _ (R2 p) (F2 p) hcore hL.2.2.1 j (p.v₀ j _) ((fw2 p).hv₀ j _).1 _ _ _ _ _ _ hk
    (F2 p).P0 (F2 p).ψ0⁻¹ (h * z) _ u hu x hx
  have hmem : x' ∈ thetaBase (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) :=
    Submodule.subset_span ⟨_, φ, hk.isKernel, h * z, hhz, _, hy', fun v => by rw [one_smul]; exact hx' v⟩
  have hs0 : ∀ y', series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z)
      ((R2 p).ioP j (PiTensorProduct.tprod ℂ u) y') =
        singleSeries (R2 p) j (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z) y' u := fun y' => by
    funext g'
    rw [series_apply, hBo.fock_eq]
    rfl
  have hs := hs0 (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m • y)
  rw [map_smul, hyio, map_smul, map_smul, smul_smul] at hs
  have key : rdAt p w j hρ ν g = (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) • ν⁻¹ •
      adForm (R2 p) j x' (fun τ => u τ) := by
    rw [hg, h2 ρ hρ hpin hfit.level h Q, hser, map_smul, hx' u, ← hs, map_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  rcases h5 ρ hρ e he1 he2 ν hν rd hcan u hu g x' _ key with rfl | ⟨b, hb, hgb⟩
  · rw [TensorProduct.tmul_zero]
    exact zero_mem _
  · obtain ⟨-, k, hk1, -⟩ := hcA
    have hζ : IsIntegral ℤ (ν / c) := IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
      rw [div_pow, hνc, div_self (pow_ne_zero _ hc)]
      exact isIntegral_one)
    obtain ⟨o, ho⟩ := exists_of_integral e hU (b := b) (k := k + m) (by
      have e3 : ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (k + m) * (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
          (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ k * cA) * (ν / c) := by
        rw [pow_add]
        field_simp
      rw [hb, e3]
      exact hk1.mul hζ)
    rw [hgb, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x', hmem, rfl⟩)

theorem baseLat_le_realBase {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} {rd : Can p w j} (hfit : Fit p w j hρ ν)
    (hinj : Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hsm : ∀ h ∈ GfC (Vc D j), ∀ Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h, ∀ g,
      rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q →
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd) :
    baseLat p w j hρ ν ≤ realBase p rd := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ realBase p rd := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨g, hg⟩ := hfit.rat.1 s h Q ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      exact ⟨g, hg, hsm h hd.fin Q hQ g hg⟩
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add (f := _), e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen h P hd.mem)
  have e : f = g := hinj (hf.trans hg.symm)
  rw [e]
  exact hm

end Point

end GlobalTheory.BigOn.Exp.SerBase

namespace GlobalTheory.BigOn.Exp

end GlobalTheory.BigOn.Exp
