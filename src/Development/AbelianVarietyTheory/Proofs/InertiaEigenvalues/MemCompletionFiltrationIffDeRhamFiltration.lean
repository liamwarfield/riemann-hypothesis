module

public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrisInclIBEqDeRhamInclID
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LatticeActionMemFilZeroDeRham
public import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffDeRhamPlusBasisTensorLatticeFree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
theorem _root_.GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (κ : Type) [Fintype κ] (b : Module.Basis κ ↥(OL LL) ↥T.L.T), (∀ v : T.V ⊗[ℚ_[l]] Pl.R.BdR, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : κ → OD l ↥(OL LL), v = ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR))) ∧ ∀ d : κ → OD l ↥(OL LL), ∑ k, act (d k) (((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) = 0 → ∀ k, d k = 0 := by
  intro l _ LL T Pl AI Td act hA κ _ b
  refine ⟨fun v => ⟨UpperTheory.KN.exists_BdRPlus_coeffs_of_mem_filZero_deRham l LL T Pl AI Td act hA κ b v, ?_⟩,
    UpperTheory.KN.linearIndependent_Ql_productBasis_of_Zl_lattice l LL T Pl AI Td act hA κ b⟩
  rintro ⟨d, rfl⟩
  exact Submodule.sum_mem _ fun k _ => UpperTheory.KN.latticeAction_mem_filZero_deRham l LL T Pl AI Td act hA (d k) _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationV
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationV
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKReal.PiSys

theorem iD_const_Ehat_eq_tmul (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type)
    [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [CompleteSpace K]
    (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) :
    ϖ.iD t K (fun _ => Ehat O K l e) = (1 : O) ⊗ₜ[ℤ_[l]] GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)) := by
  rw [iD, glue_const, Ehat, iHat_ofAl]
  exact (ϖ.iAl_of_mem O K (E_mem l e _) _).trans (congrArg (toOD l O) (ϖ.iA_E a O K))

end GlobalTheory.BKReal.PiSys

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime]

theorem ev_eis_assoc_xi {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) {ε : Per.Fl l} (hE : GlobalTheory.MemLoc.IsEps ε) :
    (∃ c : Per.Ainf l, c * GlobalTheory.MemLoc.xi ε = ϖ.ev a (eis l a e)) ∧
      ∃ c' : Per.Ainf l, c' * ϖ.ev a (eis l a e) = GlobalTheory.MemLoc.xi ε := by
  have hsp := (ϖ.span_ev_eis a).trans (GlobalTheory.MemLoc.ker_theta_eq_span_xi hE)
  refine ⟨Ideal.mem_span_singleton'.1 ?_, Ideal.mem_span_singleton'.1 ?_⟩
  · rw [← hsp]; exact Ideal.mem_span_singleton_self _
  · rw [hsp]; exact Ideal.mem_span_singleton_self _

theorem isUnit_and_mem_FilD_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) :
    IsUnit (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Per.BdR l), x ∈ Per.FilD l j ↔
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ Per.FilD l (j + 1) := by
  obtain ⟨ζ, ε, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨⟨c, hc⟩, ⟨c', hc'⟩⟩ := ev_eis_assoc_xi (a := a) ϖ hE
  set U := (GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE).unit with hUdef
  have hU : (U : Per.BdR l) = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (GlobalTheory.MemLoc.xi ε)) :=
    IsUnit.unit_spec _
  have hα : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c) * (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc]
  have hβ : algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) = (U : Per.BdR l) := by
    rw [hU, ← map_mul, ← map_mul, hc']
  refine ⟨IsUnit.of_mul_eq_one
    (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') * ((U⁻¹ : (Per.BdR l)ˣ) : Per.BdR l)) ?_, ?_⟩
  · rw [← mul_assoc, mul_comm _ (algebraMap _ _ (GlobalTheory.MemLoc.aDp l c')), hβ, Units.mul_inv]
  intro j x
  rw [GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff hE, ← hUdef]
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c * w, ?_⟩
    rw [hα, _root_.zpow_add_one, Units.val_mul, map_mul]
    ring
  · rintro ⟨w, hw⟩
    refine ⟨GlobalTheory.MemLoc.aDp l c' * w, ?_⟩
    have h2 : (U : Per.BdR l) * x = (U : Per.BdR l) * (((U ^ j : (Per.BdR l)ˣ) : Per.BdR l) *
        algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c' * w)) := by
      calc (U : Per.BdR l) * x = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x) := by
              rw [← mul_assoc, hβ]
        _ = algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l c') *
            (((U ^ (j + 1) : (Per.BdR l)ˣ) : Per.BdR l) * algebraMap (Per.BdRp l) (Per.BdR l) w) := by rw [hw]
        _ = _ := by rw [_root_.zpow_add_one, Units.val_mul, map_mul]; ring
    exact U.isUnit.mul_left_cancel h2

variable {Pl : LocPrime l} {AI : LocAinf l Pl} (Td : LocTied l Pl AI)

theorem isUnit_and_mem_Fil_iff {a e : ℕ} [NeZero a] [NeZero e] (ϖ : PiSys l e) (K : FinExt l) :
    IsUnit (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) ∧
      ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔
        GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) * x ∈ (Pl.PD K).Fil (j + 1) := by
  obtain ⟨hu, hF⟩ := isUnit_and_mem_FilD_iff (l := l) (a := a) ϖ
  have hc : Td.eD (GlobalTheory.BKGal.JumpDR.cD Td (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e)))) =
      algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l (ϖ.ev a (eis l a e))) :=
    RingEquiv.apply_symm_apply _ _
  refine ⟨?_, fun j x => ?_⟩
  · have := hu.map (Td.eD.symm : Per.BdR l →+* Pl.R.BdR)
    rw [← hc] at this
    simpa using this
  · rw [Td.fil, Td.fil, map_mul, hc]
    exact hF j _

section Abstract

variable {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem map_mem_FilV (K : FinExt l) (j k : ℤ) (g : Pl.R.BdR →ₗ[ℚ_[l]] Pl.R.BdR)
    (hg : ∀ b ∈ (Pl.PD K).Fil j, g b ∈ (Pl.PD K).Fil k) (x : V ⊗[ℚ_[l]] Pl.R.BdR)
    (hx : x ∈ FilV (Pl.PD K) (LL := LL) (V := V) j) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) g x ∈ FilV (Pl.PD K) (LL := LL) (V := V) k := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | tmul v b => exact ⟨v ⊗ₜ ⟨g b.1, hg _ b.2⟩, rfl⟩
  | add y z hy hz => simp only [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem map_mulLeft_comp (r s : Pl.R.BdR) (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] r)
      (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] s) x) =
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (r * s)) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp [mul_assoc]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem map_mulLeft_one (x : V ⊗[ℚ_[l]] Pl.R.BdR) :
    AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] (1 : Pl.R.BdR)) x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v b => simp
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

end Abstract

end GlobalTheory.BKReal.EhatShift

namespace GlobalTheory.BKReal.EhatShift

variable {l : ℕ} [Fact l.Prime] {Pl : LocPrime l}
    {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem bijective_and_mem_FilV_iff_of_mul (K : FinExt l) (ξ : Pl.R.BdR) (hu : IsUnit ξ)
    (hF : ∀ (j : ℤ) (x : Pl.R.BdR), x ∈ (Pl.PD K).Fil j ↔ ξ * x ∈ (Pl.PD K).Fil (j + 1))
    (f : V ⊗[ℚ_[l]] Pl.R.BdR →+ V ⊗[ℚ_[l]] Pl.R.BdR) (hf : ∀ v c, f (v ⊗ₜ[ℚ_[l]] c) = v ⊗ₜ[ℚ_[l]] (ξ * c)) :
    Function.Bijective f ∧ ∀ (y : V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ),
      y ∈ FilV (Pl.PD K) (LL := LL) (V := V) j ↔ f y ∈ FilV (Pl.PD K) (LL := LL) (V := V) (j + 1) := by
  have hAM : ∀ y, f y = AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] ξ) y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => rw [hf, AlgebraTensorModule.map_tmul, LinearMap.id_apply, LinearMap.mulLeft_apply]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hl : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (f y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.val_inv_mul, map_mulLeft_one]
  have hr : ∀ y, f (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) y) = y := fun y => by
    rw [hAM, map_mulLeft_comp, IsUnit.mul_val_inv, map_mulLeft_one]
  refine ⟨Function.bijective_iff_has_inverse.2 ⟨_, hl, hr⟩, fun y j => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hAM]
    exact map_mem_FilV K j (j + 1) _ (fun b hb => (hF j b).1 hb) y h
  · have := map_mem_FilV K (j + 1) j
      (LinearMap.mulLeft ℚ_[l] ((hu.unit⁻¹ : (Pl.R.BdR)ˣ) : Pl.R.BdR)) (fun b hb => by
        rw [hF j, LinearMap.mulLeft_apply, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
        exact hb) _ h
    rwa [hl] at this

end GlobalTheory.BKReal.EhatShift


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  intro l _ a e _ _ ϖ LL _ _ T Pl AI Td A hA
  rw [GlobalTheory.BKReal.PiSys.iD_const_Ehat_eq_tmul l a e ↥(OL LL) ↥LL.1 (thetaW a LL) ϖ]
  obtain ⟨hu, hF⟩ := GlobalTheory.BKReal.EhatShift.isUnit_and_mem_Fil_iff Td (a := a) ϖ (Formalism.MainNotions.ElementDenominator.qlExt l)
  refine GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff_of_mul _ _ hu hF _ fun v c => ?_
  rw [hA]
  simp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinMulBijectiveShiftsFiltrationVStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → Function.Bijective (A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e))) ∧ ∀ (y : T.V ⊗[ℚ_[l]] Pl.R.BdR) (j : ℤ), y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j) ↔ A (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j + 1) := by
  first | exact @GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | exact GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff | (intros; apply GlobalTheory.BKReal.EhatShift.bijective_and_mem_FilV_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhat
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem E_pow_mem_RpiE (N : ℕ) : E K l e ^ N ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (pow_mem (E_mem l e (A O K)) N))

theorem E_mem_RpiE : E K l e ∈ RpiE O K l e :=
  le_away _ _ (A_le_Rpi l e (E_mem l e (A O K)))

theorem hat_E_pow (N : ℕ) :
    hat O l e (E K l e ^ N) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N := by
  induction N with
  | zero => simpa using (hat_coe (O := O) (K := K) l e 1).trans (map_one _)
  | succ n ih =>
    rw [pow_succ, hat_mul l e (E_pow_mem_RpiE n) E_mem_RpiE, ih, hat_E, pow_succ]

theorem main [NeZero a] (P : PhiMod O K l e a ι) :
    ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e), ∀ τ j i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i) := by
  choose n hn using fun p : ZMod a × ι × ι => mem_away.1 (P.mxInv_mem p.1 p.2.1 p.2.2)
  have hN : ∀ p : ZMod a × ι × ι, E K l e ^ Finset.univ.sup n * P.mxInv p.1 p.2.1 p.2.2 ∈ A O K := by
    intro p
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := n) (Finset.mem_univ p))
    rw [hc, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) c) (by simpa using hn p)
  refine ⟨Finset.univ.sup n, fun τ j i => ofA O K l e ⟨_, hN (τ, j, i)⟩, fun τ j i => ?_⟩
  rw [← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

end Gen

end GlobalTheory.BK.CoordInv

open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P
  exact main P
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEisensteinPowMulPhiMatrixInvAhatStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), ∃ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i) := by
  first | exact @GlobalTheory.BK.coordE_mxInv | exact GlobalTheory.BK.coordE_mxInv | (intros; apply GlobalTheory.BK.coordE_mxInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisin
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisin
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.IdentRank

theorem basis_of_baseChange {O R N ι : Type} [CommRing O] [CommRing R] [Algebra O R] [Nontrivial R]
    [AddCommGroup N] [Module O N] [Module.Free O N] [Module.Finite O N] [Fintype ι]
    (j : (ι → R) ≃ₗ[R] R ⊗[O] N) : Nonempty (Module.Basis ι O N) := by
  classical
  have : Nontrivial O := (algebraMap O R).domain_nontrivial
  let b := Module.Free.chooseBasis O N
  have h1 := Module.finrank_eq_card_basis (Algebra.TensorProduct.basis R b)
  have h2 := j.finrank_eq
  rw [Module.finrank_fintype_fun_eq_card, h1] at h2
  exact ⟨b.reindex (Fintype.equivOfCardEq h2.symm)⟩

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I
  have := T.L.free
  have : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.2 T.L.fg
  obtain ⟨hs, hk, -⟩ := GlobalTheory.ArtinSchreierWitt.main l
  haveI : Module.Flat ℤ_[l] ↥(OL LL) := Module.Flat.of_free
  obtain ⟨-, -, h3⟩ := GlobalTheory.WittTensorFixed.baseChange_flat (O := ↥(OL LL)) (frobW l) hs hk
    (GlobalTheory.WittTensorFixed.algebraMap_WCb_injective l)
  have : Nontrivial (OW l ↥(OL LL)) := h3.nontrivial
  exact basis_of_baseChange I.j

end GlobalTheory.BKGal.IdentRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeBasisIndexedByBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL), Ident (thetaW a LL) ϖ P T → Nonempty (Module.Basis ι ↥(OL LL) ↥T.L.T) := by
  first | exact @GlobalTheory.BKGal.IdentRank.main | exact GlobalTheory.BKGal.IdentRank.main | (intros; apply GlobalTheory.BKGal.IdentRank.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplus
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinFiltrationSpanDeRhamLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (act : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), act (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (α β : ℕ), (∀ v ∈ P.L, E ↥LL.1 l e ^ α • v ∈ P.M) → (∀ v ∈ P.M, E ↥LL.1 l e ^ β • v ∈ P.L) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1) (w : T.V ⊗[ℚ_[l]] Pl.R.BdR), w ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) ((β : ℤ)) ↔ ∃ d : ι → OD l ↥(OL LL), w = ∑ i, act (d i) (∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1)))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T I jB Pl AI Td hC X hX act hA α β _ _ hβ w
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  have hb0 := (GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b).1
  obtain ⟨m, m', u, r, hu, hm, hr, hrm⟩ := UpperTheory.KN.exists_unit_invertible_matrix_identification_basis l a e ϖ LL ι P T I b
  have hf := UpperTheory.KN.crisComparison_image_eisensteinPow_phiInvColumns l a e ϖ LL ι P T I jB Pl AI Td hC X hX act hA b m u r hu hr hrm β hβ
  exact UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange _ _ act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j))
    hshift ι β
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) m m' hm hf hb0 w
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordinatesEqOfEisensteinPowMulInverseMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordinatesEqOfEisensteinPowMulInverseMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BK.CoordInv

section Gen

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_ofA_of_injective [NeZero a] (hinj : Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)))
    (P : PhiMod O K l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (hβ : ∀ τ j i, E K l e ^ β * P.mxInv τ j i ∈ A O K) (τ : ZMod a) (j i : ι) :
    y τ j i = ofA O K l e ⟨E K l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  apply hinj
  rw [hy, ← hat_coe_A, hat_mul l e (E_pow_mem_RpiE _) (invE_A_le_RpiE l e (P.mxInv_mem τ j i)), hat_E_pow]

theorem algebraMap_AhatE_injective :
    Function.Injective (algebraMap (Ahat O K l e) (AhatE O K l e)) :=
  IsLocalization.injective (M := Submonoid.powers (Ehat O K l e)) _
    (Submonoid.powers_le.2 (Ehat_mem_nonZeroDivisors O K l e))

end Gen

end GlobalTheory.BK.CoordInv


open GlobalTheory.BK.CoordInv in
theorem GlobalTheory.BK.coordE_mxInv_eq_ofA : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  intro l _ a e _ _ _ LL _ _ ι _ _ P β y hy hβ τ j i
  exact eq_ofA_of_injective (algebraMap_AhatE_injective l e) P β y hy hβ τ j i
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordinatesEqOfEisensteinPowMulInverseMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∀ (hβ : ∀ τ j i, E ↥LL.1 l e ^ β * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1), ∀ τ j i, y τ j i = ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ β * P.mxInv τ j i, hβ τ j i⟩ := by
  first | exact @GlobalTheory.BK.coordE_mxInv_eq_ofA | exact GlobalTheory.BK.coordE_mxInv_eq_ofA | (intros; apply GlobalTheory.BK.coordE_mxInv_eq_ofA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndep
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndep
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory

theorem linIndep_of_mutual_span_of_indep :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)),
      (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W),
        (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) →
        (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) →
        (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) →
        ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro R W _ _ act hmul hone ι _ _ b f hb hf hbf d hd
  letI : Module R W :=
    { smul := fun r w => act r w
      one_smul := hone
      mul_smul := fun r s w => hmul r s w
      smul_zero := fun r => map_zero (act r)
      smul_add := fun r x y => map_add (act r) x y
      add_smul := fun r s w => by
        show act (r + s) w = act r w + act s w
        rw [map_add (f := _), AddMonoidHom.add_apply]
      zero_smul := fun w => by
        show act 0 w = 0
        rw [map_zero, AddMonoidHom.zero_apply] }
  have hs : ∀ (r : R) (w : W), act r w = r • w := fun _ _ => rfl
  simp only [hs] at hb hf hbf hd
  choose P hP using hf
  choose Q hQ using hbf
  have expand : ∀ c : ι → R,
      ∑ i, c i • f i = ∑ k, (Matrix.vecMul c (Matrix.of P)) k • b k := by
    intro c
    simp only [hP, Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Matrix.of_apply,
      Finset.sum_smul]
    rw [Finset.sum_comm]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext k k'
    have h0 : ∑ k'', ((Matrix.vecMul (Q k) (Matrix.of P)) k'' - (1 : Matrix ι ι R) k k'') • b k''
        = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← expand, ← hQ, Matrix.one_apply,
        ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    have := hb _ h0 k'
    rw [sub_eq_zero] at this
    rw [← this, Matrix.mul_apply]
    simp [Matrix.vecMul, dotProduct]
  have hPQ : Matrix.of P * Matrix.of Q = 1 := mul_eq_one_comm.mp hQP
  have he : Matrix.vecMul d (Matrix.of P) = 0 := by
    rw [expand] at hd
    funext k
    exact hb _ hd k
  have : d = 0 := by
    rw [← Matrix.vecMul_one d, ← hPQ, ← Matrix.vecMul_vecMul, he, Matrix.zero_vecMul]
  intro i
  rw [this]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfMutualSpanOfIndepStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_of_mutual_span_of_indep : ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b f : ι → W), (∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) → (∀ i, ∃ d : ι → R, f i = ∑ k, act (d k) (b k)) → (∀ k, ∃ d : ι → R, b k = ∑ i, act (d i) (f i)) → ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  first | exact @GlobalTheory.linIndep_of_mutual_span_of_indep | exact GlobalTheory.linIndep_of_mutual_span_of_indep | (intros; apply GlobalTheory.linIndep_of_mutual_span_of_indep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplus
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis {R W : Type} [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W))
    (hmul : ∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) (hone : ∀ w : W, act 1 w = w) (eD : R)
    (hbij : Function.Bijective (act eD)) (F : ℤ → W → Prop) (hshift : ∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y))
    {ι : Type} [Fintype ι] [DecidableEq ι] (β β₀ : ℕ) (g h b : ι → W) (hg : ∀ i, act (eD ^ β₀) (g i) = h i)
    (hspan : ∀ w, F ((β₀ + β : ℕ) : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i))
    (hb0 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k))
    (hbi : ∀ d : ι → R, ∑ k, act (d k) (b k) = 0 → ∀ k, d k = 0) :
    ∃ f : ι → W, (∀ i, act (eD ^ β) (f i) = g i) ∧ (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (f i)) ∧
      ∀ d : ι → R, ∑ i, act (d i) (f i) = 0 → ∀ i, d i = 0 := by
  have hcomm : ∀ (d d' : R) (w : W), act d (act d' w) = act d' (act d w) := by
    intro d d' w
    rw [← hmul, ← hmul, mul_comm]
  have hpow : ∀ (n : ℕ) (w : W), act (eD ^ n) w = (act eD)^[n] w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, hone]; rfl
    | succ n ih => intro w; rw [pow_succ', hmul, ih, Function.iterate_succ_apply']
  have hinj : ∀ n : ℕ, Function.Injective (act (eD ^ n)) := by
    intro n x x' hxx
    rw [hpow, hpow] at hxx
    exact (hbij.1.iterate n) hxx
  have hsh : ∀ (n : ℕ) (w : W) (j : ℤ), F j w ↔ F (j + n) (act (eD ^ n) w) := by
    intro n
    induction n with
    | zero => intro w j; rw [pow_zero, hone, Nat.cast_zero, add_zero]
    | succ n ih =>
      intro w j
      rw [ih w j, hshift (act (eD ^ n) w) (j + n), pow_succ', hmul, Nat.cast_succ, ← add_assoc]
  have hsingle : ∀ (v : ι → W) (i : ι), ∑ k, act ((Pi.single i (1 : R) : ι → R) k) (v k) = v i := by
    intro v i
    rw [Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, map_zero, AddMonoidHom.zero_apply])
      (fun h => (h (Finset.mem_univ i)).elim), Pi.single_eq_same, hone]
  let ginv : W → W := (Equiv.ofBijective _ hbij).symm
  have hginv : ∀ x, act eD (ginv x) = x := fun x => (Equiv.ofBijective _ hbij).apply_symm_apply x
  have h1 : ∀ i, act (eD ^ β) (ginv^[β] (g i)) = g i := by
    intro i
    rw [hpow]
    exact Function.RightInverse.iterate hginv β _
  have h2 : ∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ i, act (d i) (ginv^[β] (g i)) := by
    have hf : ∀ i, act (eD ^ (β₀ + β)) (ginv^[β] (g i)) = h i := by
      intro i
      rw [pow_add, hmul, hpow β, Function.RightInverse.iterate hginv β, hg]
    intro v
    rw [hsh (β₀ + β) v 0, zero_add, hspan]
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, hinj (β₀ + β) ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hd, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcomm, hf i]
  refine ⟨fun i => ginv^[β] (g i), h1, h2, ?_⟩
  refine GlobalTheory.T.linearIndependent_of_mutual_span_of_indep R W act hmul hone ι b _ hbi ?_ ?_
  · intro i
    exact (hb0 _).1 ((h2 _).2 ⟨Pi.single i 1, (hsingle (fun i => ginv^[β] (g i)) i).symm⟩)
  · intro k
    exact (h2 _).1 ((hb0 _).2 ⟨Pi.single k 1, (hsingle b k).symm⟩)


set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem GlobalTheory.BKGal.JumpDR.basis_images : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  intro hF l _ a e _ _ ϖ LL _ _ hl2 ι _ _ P T I jB Pl AI Td hC X hX act hA β y hy
  obtain ⟨hmul, hone⟩ := GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA
  obtain ⟨hbij, hshift⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td act hA
  obtain ⟨α, β0, hα, hβ0⟩ := P.exists_exponents
  have hLM1 : ∀ v ∈ P.M, E ↥LL.1 l e ^ (β0 + β) • v ∈ P.L := by
    intro v hv
    have := P.L.smul_mem (⟨_, pow_mem (E_mem l e _) β⟩ : A ↥(OL LL) ↥LL.1) (hβ0 v hv)
    rw [pow_add, mul_comm, mul_smul]
    exact this
  have hβ1 : ∀ τ j i, E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i ∈ A ↥(OL LL) ↥LL.1 := by
    intro τ j i
    have hv : (fun (_ : ZMod a) (i' : ι) => if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ P.M := by
      refine mem_tot.2 fun τ' i' => ?_
      show (if i' = i then (1 : (↥LL.1)⟦X⟧) else 0) ∈ A ↥(OL LL) ↥LL.1
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h2 := (P.mem_extc_iff.1 (mem_tot.1 (hLM1 _ hv) τ)) j
    convert h2 using 1
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hy1 : ∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e)
      (Ehat ↥(OL LL) ↥LL.1 l e) ^ (β0 + β) * hat ↥(OL LL) l e (P.mxInv τ j i) := fun τ j i =>
    (map_mul _ _ _).trans ((congrArg₂ (· * ·) (map_pow _ _ _) (hy τ j i)).trans
      ((mul_assoc _ _ _).symm.trans (congrArg (· * _) (pow_add _ _ _).symm)))
  have hyA := GlobalTheory.T.coordinates_eq_of_eisensteinPow_mul_inverse_matrix l a e ϖ LL ι P (β0 + β) (fun τ j i => Ehat ↥(OL LL) ↥LL.1 l e ^ β0 * y τ j i) hy1 hβ1
  have hg : ∀ i, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)
      (∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) =
      ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))) := by
    intro i
    refine (map_sum (act (ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0)) _ _).trans
      (Finset.sum_congr rfl fun j _ => ?_)
    refine (hmul _ _ _).symm.trans (congrArg (fun z => act z (X (jB (Pi.single j 1)))) ?_)
    refine Eq.trans ?_ (PiSys.iD_ofA (thetaW a LL) ↥LL.1 ϖ _)
    have hpt : (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β0 * (fun τ => y τ j i) =
        fun τ => ofA ↥(OL LL) ↥LL.1 l e ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩ :=
      funext fun τ => hyA τ j i
    exact (congrArg (· * ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i))
      (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) β0).symm).trans
      ((map_mul (ϖ.iD (thetaW a LL) ↥LL.1) _ _).symm.trans (congrArg (ϖ.iD (thetaW a LL) ↥LL.1) hpt))
  have hspan := GlobalTheory.T.breuilKisin_filtration_span_deRhamLattice hF l a e ϖ LL hl2 ι P T I jB Pl AI Td hC X hX act hA α (β0 + β) hα hLM1 hβ1
  obtain ⟨b⟩ := GlobalTheory.T.galoisLattice_basis_indexed_by_breuilKisin l a e ϖ LL ι P T I
  obtain ⟨hb0, hbi⟩ := GlobalTheory.T.coeffDeRhamPlus_basis_tensorLattice_free l LL T Pl AI Td act hA ι b
  exact GlobalTheory.BKGal.JumpDR.BasisGlue.exists_basis act hmul hone _ hbij
    (fun (j : ℤ) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) => v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (j)) hshift β β0
    (fun i => ∑ j, act (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1))))
    (fun i => ∑ j, act (toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1
        (fun τ => ⟨E ↥LL.1 l e ^ (β0 + β) * P.mxInv τ j i, hβ1 τ j i⟩))) (X (jB (Pi.single j 1))))
    (fun k => ((b k : ↥T.L.T) : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.BdR)) hg hspan hb0 hbi

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBasisImagesBasisBdRplusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (β : ℕ) (y : ZMod a → ι → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (y τ j i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ β * hat ↥(OL LL) l e (P.mxInv τ j i)) → ∃ f : ι → T.V ⊗[ℚ_[l]] Pl.R.BdR, (∀ i, A ((ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e)) ^ β) (f i) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => y τ j i)) (X (jB (Pi.single j 1)))) ∧ (∀ v, v ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) (0) ↔ ∃ d : ι → OD l ↥(OL LL), v = ∑ i, A (d i) (f i)) ∧ ∀ d : ι → OD l ↥(OL LL), ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0 := by
  exact @GlobalTheory.BKGal.JumpDR.basis_images
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRImageBcrisEqAinfHatCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {W : Type} [AddCommGroup W] (Y : TW (OB l O) T →+ W)
    (act : OD l O →+ (W →+ W)) (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (C : GlobalTheory.MemLoc.Core l)
    (hact : ∀ (b : OB l O) (y : OD l O), iotaO O C b = dRO l O y → ∀ z : TW (OB l O) T, Y (b • z) = act y (Y z))
    (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e)
    (hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) =
      ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) :
    ∑ k, act (ϖ.iD t K (s k)) (Y (jB (toBcris t ϖ P (m k)))) =
      ∑ j, act (ϖ.iD t K (fun τ => c τ j)) (Y (jB (Pi.single j 1))) := by
  have hco := UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix l a e O K t ϖ ι P n s m c hc
  have h1 : ∀ k, Y (jB (toBcris t ϖ P (m k))) = ∑ j, act (ϖ.iD t K
      (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)))
      (Y (jB (Pi.single j 1))) := by
    intro k
    have h2 : toBcris t ϖ P (m k) = ∑ j, ϖ.iB t K
        (coordL P (invL l (S O K e)) (m k) j) • (Pi.single j 1 : ι → OB l O) := by
      funext i
      rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jB.map_smul]
    exact hact _ _ (UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C _) _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h1, hco, map_sum, map_mul, AddMonoidHom.finsetSum_apply, hmul]
  exact Finset.sum_comm

theorem _root_.GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (c τ j) = ∑ i, hat ↥(OL LL) l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => c τ j)) (X (jB (Pi.single j 1))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T jB Pl AI Td Y hY act hA n s m c hc
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact gen (thetaW a LL) ϖ P T jB Y act (GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA).1 C
    (UpperTheory.KN.crysLattice_bdRPlus_action_compat l LL T Pl AI Td Y hY act hA C) n s m c hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR

section General

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K] [NeZero a]
  {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_Ehat_pow_mul (w : ZMod a → ι → AhatE O K l e) :
    ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i,
      algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) =
        algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * w τ i := by
  classical
  choose r z hz using fun p : ZMod a × ι => IsLocalization.Away.surj (Ehat O K l e) (w p.1 p.2)
  refine ⟨Finset.univ.sup r, fun τ i => Ehat O K l e ^ (Finset.univ.sup r - r (τ, i)) * z (τ, i),
    fun τ i => ?_⟩
  have hle : r (τ, i) ≤ Finset.univ.sup r := Finset.le_sup (Finset.mem_univ _)
  rw [map_mul, map_pow, ← hz (τ, i), mul_left_comm, ← pow_add, Nat.sub_add_cancel hle, mul_comm]

end General

theorem hsum_mul_Ehat_pow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P n s m
  exact exists_Ehat_pow_mul (GlobalTheory.BKGal.JumpDR.hsum P s fun k => (m k).1)

end GlobalTheory.BKGal.JumpDR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HsumMulEisensteinCompletionPowIntegralStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl), ∃ (N : ℕ) (x : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), ∀ τ i, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (x τ i) = algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (Ehat ↥(OL LL) ↥LL.1 l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
  first | exact @GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | exact GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow | (intros; apply GlobalTheory.BKGal.JumpDR.hsum_mul_Ehat_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltration
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.JumpDR.CmpFil

theorem amulG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ∀ o o', ι' (o * o') = ι' o * ι' o') (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (x y : OD l O) (v : V ⊗[ℚ_[l]] R) : A (x * y) v = A x (A y v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c =>
    induction x using TensorProduct.induction_on with
    | zero => simp only [zero_mul, map_zero, AddMonoidHom.zero_apply]
    | add x x' hx hx' => simp only [add_mul, map_add (f := _), AddMonoidHom.add_apply, hx, hx']
    | tmul o b =>
      induction y using TensorProduct.induction_on with
      | zero => simp only [mul_zero, map_zero, AddMonoidHom.zero_apply]
      | add y y' hy hy' => simp only [mul_add, map_add (f := _), AddMonoidHom.add_apply, hy, hy']
      | tmul o' b' =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hA, hA, hA, map_mul, mul_assoc, h1, mul_smul]

theorem aoneG {l : ℕ} [Fact l.Prime] {O K V R : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K]
    [AddCommGroup V] [Module K V] [Module ℚ_[l] V] [CommRing R] [Algebra ℚ_[l] R] (ι' : O → K)
    (h1 : ι' 1 = 1) (cD : Per.BdRp l →+* R)
    (A : OD l O →+ (V ⊗[ℚ_[l]] R →+ V ⊗[ℚ_[l]] R))
    (hA : ∀ (o : O) (b : Per.BdRp l) (v : V) (c : R), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = (ι' o • v) ⊗ₜ[ℚ_[l]] (cD b * c))
    (v : V ⊗[ℚ_[l]] R) : A 1 v = v := by
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | tmul v c => rw [Algebra.TensorProduct.one_def, hA, map_one, one_mul, h1, one_smul]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem amulL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (x y : OD l ↥(OL LL)) (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A (x * y) v = A x (A y v) :=
  amulG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) (fun _ _ => rfl) (GlobalTheory.BKGal.JumpDR.cD Td) A hA x y v

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem aoneL {l : ℕ} [Fact l.Prime] {LL : FinExt l} {T : QLat LL} {Pl : LocPrime l} {AI : LocAinf l Pl} {Td : LocTied l Pl AI}
    (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR))
    (hA : ∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c))
    (v : T.V ⊗[ℚ_[l]] Pl.R.BdR) : A 1 v = v :=
  aoneG (K := ↥LL.1) (fun o : ↥(OL LL) => (o : ↥LL.1)) rfl (GlobalTheory.BKGal.JumpDR.cD Td) A hA v

set_option maxHeartbeats 1000000 in
theorem coreG {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
    [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : PhiMod O K l e a ι) {W : Type} [AddCommGroup W] (A : OD l O →+ (W →+ W)) (Fil : ℤ → W → Prop)
    (amul : ∀ x y v, A (x * y) v = A x (A y v)) (aone : ∀ v, A 1 v = v)
    (hbij : Function.Bijective (A (ϖ.iD t K (fun _ => Ehat O K l e))))
    (hS : ∀ (y : W) (j : ℤ), Fil j y ↔ Fil (j + 1) (A (ϖ.iD t K (fun _ => Ehat O K l e)) y))
    (gB : ι → W) (β : ℕ) (y : ZMod a → ι → ι → Ahat O K l e)
    (hy : ∀ τ j i, algebraMap (Ahat O K l e) (AhatE O K l e) (y τ j i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ β * hat O l e (P.mxInv τ j i))
    (f : ι → W) (hf1 : ∀ i, A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i) = ∑ j, A (ϖ.iD t K (fun τ => y τ j i)) (gB j))
    (hspan : ∀ v, Fil 0 v ↔ ∃ d : ι → OD l O, v = ∑ i, A (d i) (f i))
    (hind : ∀ d : ι → OD l O, ∑ i, A (d i) (f i) = 0 → ∀ i, d i = 0)
    {n : ℕ} (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (g : Fin n → W)
    (hC : ∀ (s' : Fin n → ZMod a → Ahat O K l e) (c : ZMod a → ι → Ahat O K l e), (∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD t K (s' k)) (g k) = ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j))
    (hE1 : ∃ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i)
    (j : ℤ) :
    GlobalTheory.BKGal.JumpDR.InEhat O K l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ Fil j (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
  classical
  have hbijN : ∀ N : ℕ, Function.Bijective (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) := by
    intro N
    induction N with
    | zero =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ 0)) = id := funext fun v => by rw [pow_zero]; exact aone v
      rw [h0]; exact Function.bijective_id
    | succ N ih =>
      have h0 : ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1))) = ⇑(A (ϖ.iD t K (fun _ => Ehat O K l e))) ∘ ⇑(A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N)) :=
        funext fun v => by rw [pow_succ', amul]; rfl
      rw [h0]; exact hbij.comp ih
  have hSh : ∀ (N : ℕ) (y : W) (j : ℤ), Fil j y ↔ Fil (j + N) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by
    intro N
    induction N with
    | zero => intro y j; rw [pow_zero, aone, Nat.cast_zero, add_zero]
    | succ N ih =>
      intro y j
      have e1 : (j + ((N + 1 : ℕ) : ℤ)) = (j + N) + 1 := by push_cast; ring
      have e2 : A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + 1)) y = A (ϖ.iD t K (fun _ => Ehat O K l e)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) y) := by rw [pow_succ', amul]
      rw [e1, e2]
      exact (ih y j).trans (hS _ _)
  have Fb : ∀ (d : ι → OD l O) (kk : ℕ), Fil kk (∑ i, A (d i) (f i)) ↔ ∀ i, d i ∈ Ideal.span {(ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk} := by
    intro d kk
    constructor
    · intro hd
      obtain ⟨v', hv'⟩ := (hbijN kk).2 (∑ i, A (d i) (f i))
      have h0 : Fil 0 v' := (hSh kk v' 0).2 (by rw [hv', zero_add]; exact hd)
      obtain ⟨z, rfl⟩ := (hspan v').1 h0
      have h4 : ∑ i, A (d i - (ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk * z i) (f i) = 0 := by
        simp only [map_sub, AddMonoidHom.sub_apply, Finset.sum_sub_distrib, amul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hv', sub_self]
      intro i
      have h5 := hind _ h4 i
      rw [sub_eq_zero] at h5
      rw [h5]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    · intro hd
      choose z hz using fun i => Ideal.mem_span_singleton'.1 (hd i)
      have h6 : ∑ i, A (d i) (f i) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ kk) (∑ i, A (z i) (f i)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← hz i, mul_comm, amul]
      have h7 := (hSh kk _ 0).1 ((hspan _).2 ⟨z, rfl⟩)
      rw [zero_add] at h7
      rw [h6]; exact h7
  have key : ∀ (N : ℕ) (x : ZMod a → ι → Ahat O K l e), (∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) →
      A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ N) (∑ k, A (ϖ.iD t K (s k)) (g k)) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i) := by
    intro N x hx
    let s' : Fin n → ZMod a → Ahat O K l e := fun k => (fun _ => Ehat O K l e) ^ (N + β) * s k
    let c : ZMod a → ι → Ahat O K l e := fun τ j => ∑ i, y τ j i * x τ i
    have hw : ∀ τ i, GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N + β) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i
      simp only [GlobalTheory.BKGal.JumpDR.hsum, s', Pi.mul_apply, Pi.pow_apply, map_mul, map_pow, Finset.mul_sum, mul_assoc]
    have hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) = ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s' (fun k => (m k).1) τ i := by
      intro τ j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [c, map_sum, map_mul, hy, hx, hw]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hC' := hC s' c hc
    have h1 : ∑ k, A (ϖ.iD t K (s' k)) (g k) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ (N + β)) (∑ k, A (ϖ.iD t K (s k)) (g k)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [s', map_mul, map_pow]
      rw [amul]
    have h2' : ∑ j, A (ϖ.iD t K (fun τ => c τ j)) (gB j) = ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) := by
      have h3 : ∀ j, (fun τ => c τ j) = ∑ i, (fun τ => x τ i) * (fun τ => y τ j i) := by
        intro j; funext τ; simp only [c, Finset.sum_apply, Pi.mul_apply, mul_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [h3, map_sum, AddMonoidHom.finsetSum_apply, map_mul, amul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf1 i, map_sum]
    rw [h1, h2'] at hC'
    have h3 : ∑ i, A (ϖ.iD t K (fun τ => x τ i)) (A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (f i)) = A ((ϖ.iD t K (fun _ => Ehat O K l e)) ^ β) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← amul, ← amul, mul_comm]
    rw [h3, pow_add, mul_comm, amul] at hC'
    exact (hbijN β).1 hC'
  constructor
  · rintro ⟨N, hN, hx⟩
    choose x' hx' using hx
    have hkj : (((j + N).toNat : ℕ) : ℤ) = j + N := Int.toNat_of_nonneg hN
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ (j + N).toNat * x' τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ N * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; rw [← map_pow]; exact hx' τ i
    have hK := key N x hxx
    have hmem : Fil (((j + N).toNat : ℕ) : ℤ) (∑ i, A (ϖ.iD t K (fun τ => x τ i)) (f i)) := by
      refine (Fb _ _).2 fun i => ?_
      have h8 : (fun τ => x τ i) = (fun _ => Ehat O K l e) ^ (j + N).toNat * fun τ => x' τ i := by
        funext τ; simp only [x, Pi.mul_apply, Pi.pow_apply]
      rw [h8, map_mul, map_pow]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [← hK, hkj] at hmem
    exact (hSh N _ j).2 hmem
  · intro hF
    obtain ⟨N₁, x₁, hx₁⟩ := hE1
    let x : ZMod a → ι → Ahat O K l e := fun τ i => Ehat O K l e ^ j.natAbs * x₁ τ i
    have hxx : ∀ τ i, algebraMap (Ahat O K l e) (AhatE O K l e) (x τ i) = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e) ^ (N₁ + j.natAbs) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i := by
      intro τ i; simp only [x, map_mul, map_pow, hx₁, pow_add]; ring
    have hK := key _ x hxx
    have hN : 0 ≤ j + ((N₁ + j.natAbs : ℕ) : ℤ) := by push_cast; have := neg_abs_le j; omega
    have hkj : (((j + ((N₁ + j.natAbs : ℕ) : ℤ)).toNat : ℕ) : ℤ) = j + ((N₁ + j.natAbs : ℕ) : ℤ) := Int.toNat_of_nonneg hN
    have h1 := (hSh (N₁ + j.natAbs) _ j).1 hF
    rw [hK, ← hkj] at h1
    have h2 := (Fb _ _).1 h1
    refine ⟨N₁ + j.natAbs, hN, fun τ i => ?_⟩
    obtain ⟨z, hz⟩ := PiSys.eq_Ehat_pow_mul_of_iD_mem l a e O K t ϖ _ _ (h2 i)
    refine ⟨z τ, ?_⟩
    have h9 := congrFun hz τ
    simp only [Pi.mul_apply, Pi.pow_apply] at h9
    rw [← h9, map_pow]
    exact hxx τ i

end GlobalTheory.BKGal.JumpDR.CmpFil

open GlobalTheory.BKGal.JumpDR.CmpFil in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 2000000 in
theorem GlobalTheory.BKGal.JumpDR.inEhat_iff_filV : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  intro hFont l _ a e _ _ ϖ LL _ _ h2 ι _ _ P T I jB Pl AI Td hcmp X hX A hA n s m j
  obtain ⟨hbij, hS⟩ := GlobalTheory.T.eisenstein_mul_bijective_shifts_filtrationV l a e ϖ LL T Pl AI Td A hA
  obtain ⟨β, y, hy⟩ := GlobalTheory.T.exists_eisenstein_pow_mul_phiMatrix_inv_ahat l a e ϖ LL ι P
  obtain ⟨f, hf1, hspan, hind⟩ := GlobalTheory.T.breuilKisin_basis_images_basis_BdRplus hFont l a e ϖ LL h2 ι P T I jB Pl AI Td hcmp X hX A hA β y hy
  exact coreG (thetaW a LL) ϖ P A (fun j y => y ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j)
    (amulL A hA) (aoneL A hA) hbij hS (fun j => X (jB (Pi.single j 1))) β y hy f hf1 hspan hind s m
    (fun k => X (jB (toBcris (thetaW a LL) ϖ P (m k))))
    (fun s' c h => GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates hFont l a e ϖ LL h2 ι P T jB Pl AI Td X hX A hA n s' m c h)
    (GlobalTheory.T.hsum_mul_eisensteinCompletion_pow_integral l a e ϖ LL ι P n s m) j
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletionFiltrationIffDeRhamFiltrationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completionFiltration_iff_deRhamFiltration : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI), IsCrisCmp I jB → ∀ (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (j : ℤ), GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e j (GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1)) ↔ ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) ∈ FilV (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (LL := ↥LL.1) (V := T.V) j := by
  first | exact @GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | exact GlobalTheory.BKGal.JumpDR.inEhat_iff_filV | (intros; apply GlobalTheory.BKGal.JumpDR.inEhat_iff_filV <;> assumption)
end
