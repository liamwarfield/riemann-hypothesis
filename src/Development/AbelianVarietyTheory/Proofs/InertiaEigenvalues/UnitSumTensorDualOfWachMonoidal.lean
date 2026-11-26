module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegersCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormExtensionAcris
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CloseVectorNeZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerGeneratorMatrixPerturbation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaModuleSaturationTheorem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TensorLatticeUnitPart
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Bilinear

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

end Bilinear

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L) (i' : LatHom T'.L T''.L) : Prop :=
  Function.Bijective (i.f.coprod i'.f) ∧
    ∀ z ∈ T''.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = i.f x + i'.f y

variable (W : LocWach PD LL O v n) {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.IndefiniteRowSideFullHecke.TensorLatticeUnitPart
end
end

noncomputable section

namespace GlobalTheory.Cmp.WachMonoidal

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
open GlobalTheory.IndefiniteRowSideFullHecke

section Ext

variable {O : Type} [CommRing O] (R : Type) [CommRing R] [Algebra O R]
  {M M' M'' : Type} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup M'']
  [Module O M] [Module O M'] [Module O M'']

end Ext

section Crys

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']

theorem tensorB_comp (f : V →ₗ[LL] V') (g : V' →ₗ[LL] V'') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g (CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x) =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (g.comp f) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem tensorB_id (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (LinearMap.id : V →ₗ[LL] V) x = x := by
  simp [CrystallineSubrepresentation.tensorB]

theorem tensorB_zero (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (0 : V →ₗ[LL] V') x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB]
  | add a b ha hb => simp only [map_add (f := _), ha, hb, add_zero]

theorem tensorB_add (f g : V →ₗ[LL] V') (x : V ⊗[Qp] B) :
    CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) (f + g) x =
      CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x + CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [CrystallineSubrepresentation.tensorB, add_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]; abel

theorem coe_DcrisMap {ρ : Representation LL G V} {ρ' : Representation LL G V'} {f : V →ₗ[LL] V'}
    (hf : CrystallineSubrepresentation.IsEquivariant ρ ρ' f) (x : ↥(Dcris PD ρ)) :
    (CrystallineSubrepresentation.DcrisMap PD hf x : V' ⊗[Qp] B) = CrystallineSubrepresentation.tensorB (Qp := Qp) (B := B) f x := rfl

theorem isCrys_of_equiv {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x)) (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  have h1 : CrystallineSubrepresentation.IsEquivariant ρ ρ' e.toLinearMap := he
  have h2 : CrystallineSubrepresentation.IsEquivariant ρ' ρ e.symm.toLinearMap := fun g x => by
    apply e.injective
    simp [he]
  let E : ↥(Dcris PD ρ) ≃ₗ[LL] ↥(Dcris PD ρ') :=
    LinearEquiv.ofLinear (CrystallineSubrepresentation.DcrisMap PD h1) (CrystallineSubrepresentation.DcrisMap PD h2)
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
      (by
        ext x
        simp only [LinearMap.comp_apply, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [show e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id by ext; simp, tensorB_id])
  unfold IsCrys at h ⊢
  rw [← E.finrank_eq, ← e.finrank_eq, h]

theorem finite_Dcris [FiniteDimensional LL V] {ρ : Representation LL G V} (h : IsCrys PD ρ) :
    Module.Finite LL ↥(Dcris PD ρ) := by
  rcases Nat.eq_zero_or_pos (finrank LL ↥(Dcris PD ρ)) with h0 | h0
  · have := PD.finK₀
    have hK : 0 < finrank Qp K₀ := Module.finrank_pos
    unfold IsCrys at h
    have hV : finrank LL V = 0 := by
      rw [h0] at h
      rcases Nat.mul_eq_zero.mp h.symm with h | h
      · omega
      · exact h
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    infer_instance
  · exact Module.finite_of_finrank_pos h0

theorem isCrys_prod [FiniteDimensional LL V] [FiniteDimensional LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'}
    (h : IsCrys PD ρ) (h' : IsCrys PD ρ') : IsCrys PD (ρ.prod ρ') := by
  have := finite_Dcris PD h
  have := finite_Dcris PD h'
  have e1 : CrystallineSubrepresentation.IsEquivariant ρ (ρ.prod ρ') (LinearMap.inl LL V V') := fun g x => by
    simp [Representation.prod]
  have e2 : CrystallineSubrepresentation.IsEquivariant ρ' (ρ.prod ρ') (LinearMap.inr LL V V') := fun g x => by
    simp [Representation.prod]
  have p1 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ (LinearMap.fst LL V V') := fun g x => by
    simp [Representation.prod]
  have p2 : CrystallineSubrepresentation.IsEquivariant (ρ.prod ρ') ρ' (LinearMap.snd LL V V') := fun g x => by
    simp [Representation.prod]
  let E : (↥(Dcris PD ρ) × ↥(Dcris PD ρ')) ≃ₗ[LL] ↥(Dcris PD (ρ.prod ρ')) :=
    LinearEquiv.ofLinear ((CrystallineSubrepresentation.DcrisMap PD e1).coprod (CrystallineSubrepresentation.DcrisMap PD e2))
      ((CrystallineSubrepresentation.DcrisMap PD p1).prod (CrystallineSubrepresentation.DcrisMap PD p2))
      (by
        refine LinearMap.ext fun x => Subtype.ext ?_
        simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
          Submodule.coe_add, coe_DcrisMap, tensorB_comp, LinearMap.id_apply]
        rw [← tensorB_add, show (LinearMap.inl LL V V').comp (LinearMap.fst LL V V') +
          (LinearMap.inr LL V V').comp (LinearMap.snd LL V V') = LinearMap.id by ext <;> simp,
          tensorB_id])
      (by
        refine LinearMap.ext fun x => Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.fst_comp_inl, LinearMap.fst_comp_inr, tensorB_id, tensorB_zero, add_zero]
        · simp only [LinearMap.comp_apply, LinearMap.coprod_apply, LinearMap.prod_apply, Function.prod,
            Prod.fst_add, Prod.snd_add, Submodule.coe_add, coe_DcrisMap, map_add, tensorB_comp, LinearMap.id_apply,
            LinearMap.snd_comp_inl, LinearMap.snd_comp_inr, tensorB_id, tensorB_zero, zero_add])
  unfold IsCrys at h h' ⊢
  rw [← E.finrank_eq, Module.finrank_prod, Module.finrank_prod, h, h', mul_add]

end Crys

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem isCrys_of_isSumLat {T T' T'' : LocLat G Qp LL O} (i : LatHom T.L T''.L)
    (i' : LatHom T'.L T''.L) (h : IsCrys PD T.ρ) (h' : IsCrys PD T'.ρ) (hs : TensorLatticeUnitPart.IsSumLat i i') :
    IsCrys PD T''.ρ :=
  isCrys_of_equiv PD (LinearEquiv.ofBijective (i.f.coprod i'.f) hs.1)
    (fun g x => by simp [Representation.prod, i.equiv, i'.equiv]) (isCrys_prod PD h h')



variable {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

end Generic

variable (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (H : LocHW l P)
  (F : LocFon l P AI H)

end GlobalTheory.Cmp.WachMonoidal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGaussGCTarget
noncomputable section

open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem isGauss_gC_of_le (l : ℕ) [Fact l.Prime] (ρ : ℝ) (h0 : (l : ℝ)⁻¹ ≤ ρ) (h1 : ρ < 1) :
    IsGauss l ρ (gC l ρ) := by
  have h : ∃ N, IsGauss l ρ N := GlobalTheory.GaussExt.exists_gauss_acris l ρ h0 h1
  have e : gC l ρ = Classical.choose h := by
    funext x
    simp only [gC, dif_pos h]
  rw [e]
  exact Classical.choose_spec h

theorem isGauss_gC_target : ∀ (l : ℕ) [Fact l.Prime] (ρ : ℝ), (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → IsGauss l ρ (gC l ρ) :=
  fun l _ ρ h0 h1 => isGauss_gC_of_le l ρ h0 h1

end GlobalTheory.PMon.Gauss

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmetic
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.WindowArith

theorem sg_ineq (l n : ℕ) [NeZero n] (hl : 2 ≤ l) (h : ZMod n → ℕ) (i : ZMod n) :
    h i + sg l h i + 1 ≤ l * (sg l h (i - 1) + 1) := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hshift : ∀ j : ℕ, (h (i - 1 + ((j + 1 + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1 + 1)
      = (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) / l := by
    intro j
    have e : i - 1 + ((j + 1 + 1 : ℕ) : ZMod n) = i + ((j + 1 : ℕ) : ZMod n) := by
      push_cast; ring
    rw [e, pow_succ, div_div]
  have e0 : i - 1 + ((0 + 1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hrec : (l : ℝ) * (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
      = h i + ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) := by
    rw [(summable_sg hl h (i - 1)).tsum_eq_zero_add, e0]
    simp only [hshift, tsum_div_const]
    field_simp
    ring
  have hS0 : 0 ≤ ∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1) :=
    tsum_nonneg fun j => by positivity
  have h1 := Nat.floor_le hS0
  have h2 := Nat.lt_floor_add_one
    (∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1))
  have h3 := mul_lt_mul_of_pos_left h2 hl0
  have key : (h i : ℝ) + (⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ)
      < (l : ℝ) * ((⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ : ℝ) + 1) := by
    linarith
  have key' : h i + ⌊∑' j : ℕ, (h (i + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊
      < l * (⌊∑' j : ℕ, (h (i - 1 + ((j + 1 : ℕ) : ZMod n)) : ℝ) / (l : ℝ) ^ (j + 1)⌋₊ + 1) := by
    exact_mod_cast key
  simp only [sg]
  omega

theorem eq_of_cast_eq {k : Type} [Field k] {l : ℕ} [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ u - y := ((CharP.intCast_eq_intCast k l).mp h).symm.dvd
  have := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith, h1⟩)
  linarith

private theorem cast_ne_of_mem_cloud_of_typeG {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hG : Dt.ty i = LType.G) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ y) (hy2 : y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) :
    (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu y hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hG]
  exact hm

private theorem natCast_ne_of_mem_cloud_of_bd_of_mem_range {k : Type} [Field k] {l n r : ℕ} [CharP k l] {Dt : TopData n r}
    (h3 : Dt.T3 l) {i : ZMod n} (hB : Dt.ty i = LType.Bd) {u : ℤ} (hu : u ∈ Dt.cloud i) (y : ℤ)
    (hy1 : -2 * (Dt.sg l i : ℤ) - 2 ≤ (Dt.h i : ℤ) - y)
    (hy2 : (Dt.h i : ℤ) - y ≤ (Dt.η i : ℤ) + 2 * Dt.sg l i + 3) : (u : k) ≠ (y : k) := by
  intro he
  apply h3 i u hu ((Dt.h i : ℤ) - y) hy1 hy2
  have hm : u ≡ y [ZMOD l] := (CharP.intCast_eq_intCast k l).mp he
  simp only [TopData.cloudRes, hB]
  exact Int.ModEq.sub (Int.ModEq.refl _) hm

theorem windows : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  intro k _ l n r _ _ _ Dt hT1 hT2 hT3 i
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hT1i := hT1 i
  have ht := Dt.one_le_letterBlockLength
  have hwB : Dt.w i ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨le_rfl, by omega⟩))
  have heB : Dt.w i + Dt.t - 1 ∈ Dt.lows i + block (Dt.w i) Dt.t :=
    Multiset.mem_add.2 (Or.inr (mem_block.2 ⟨by omega, by omega⟩))
  have factsG : Dt.ty i = LType.G → (∀ u ∈ Dt.lows i, 1 ≤ u ∧ u ≤ (Dt.η i : ℤ)) ∧
      1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i := fun hG =>
    ⟨fun u hu => Dt.lowG i hG u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowG i hG _ hwB).1,
      (Dt.lowG i hG _ heB).2⟩
  have factsBd : Dt.ty i = LType.Bd → (∀ u ∈ Dt.lows i, (Dt.h i : ℤ) - Dt.η i ≤ u ∧ u ≤ (Dt.h i : ℤ) - 1) ∧
      (Dt.h i : ℤ) - Dt.η i ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ (Dt.h i : ℤ) - 1 := fun hB =>
    ⟨fun u hu => Dt.lowBd i hB u (Multiset.mem_add.2 (Or.inl hu)), (Dt.lowBd i hB _ hwB).1,
      (Dt.lowBd i hB _ heB).2⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hsg := sg_ineq l n hl2 Dt.h i
    have e1 : Dt.sg l i = sg l Dt.h i := rfl
    have e2 : Dt.sg l (i - 1) = sg l Dt.h (i - 1) := rfl
    rw [e1, e2]
    zify at hsg
    linarith
  · intro u hu y hy1 hy2 he
    rcases Multiset.mem_add.1 hu with hu | hu
    · have huy : u = y := by
        cases hty : Dt.ty i
        · obtain ⟨hL, hw1, hw2⟩ := factsG hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
        · obtain ⟨hL, hw1, hw2⟩ := factsBd hty
          have := hL u hu
          exact eq_of_cast_eq he (by omega) (by omega)
      have key : ∃ β ∈ Dt.B i, |u - β| ≤ (Dt.sg l i : ℤ) + 2 := by
        by_cases hyw : y < Dt.w i
        · exact ⟨Dt.w i, mem_block.2 ⟨le_rfl, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        by_cases hye : Dt.w i + Dt.t - 1 < y
        · exact ⟨Dt.w i + Dt.t - 1, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
        · exact ⟨y, mem_block.2 ⟨by omega, by omega⟩, abs_le.2 ⟨by omega, by omega⟩⟩
      obtain ⟨β, hβ, hb⟩ := key
      have := hT2 i u hu β hβ
      linarith
    · cases hty : Dt.ty i
      · obtain ⟨-, hw1, hw2⟩ := factsG hty
        exact cast_ne_of_mem_cloud_of_typeG hT3 hty hu y (by omega) (by omega) he
      · obtain ⟨-, hw1, hw2⟩ := factsBd hty
        exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hty hu y (by omega) (by omega) he
  · intro hG
    obtain ⟨hL, hw1, hw2⟩ := factsG hG
    refine ⟨?_, ?_, hw1, hw2⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact cast_ne_of_mem_cloud_of_typeG hT3 hG hu y (by omega) (by omega) he
  · intro hB
    obtain ⟨hL, hw1, hw2⟩ := factsBd hB
    have ew : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    refine ⟨?_, ?_, by rw [ew]; omega, by rw [ew]; omega⟩
    · intro u hu y hy1 hy2 he
      rcases Multiset.mem_add.1 hu with hu | hu
      · have := hL u hu
        have huy := eq_of_cast_eq he (by omega) (by omega)
        omega
      · exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he
    · intro u hu y hy1 hy2 he
      exact natCast_ne_of_mem_cloud_of_bd_of_mem_range hT3 hB hu y (by omega) (by omega) he

end GlobalTheory.WindowArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleLetterDataWindowArithmeticStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissibleLetterData_window_arithmetic : ∀ {k : Type} [Field k] {l n r : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] (Dt : TopData n r), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ i, ((Dt.sg l i : ℤ) + 1 ≤ l * (Dt.sg l (i - 1) + 1) - Dt.h i) ∧ (∀ u ∈ Dt.U i, ∀ y : ℤ, Dt.w i - Dt.sg l i - 2 ≤ y → y ≤ Dt.w i + Dt.t + 1 + Dt.sg l i → (u : k) ≠ (y : k)) ∧ (Dt.ty i = LType.G → (∀ u ∈ Dt.U i, ∀ y : ℤ, -(Dt.sg l i : ℤ) ≤ y → y ≤ 0 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, 0 ≤ y → y ≤ Dt.η i → (u : k) ≠ (y : k)) ∧ 1 ≤ Dt.w i ∧ Dt.w i + Dt.t - 1 ≤ Dt.η i) ∧ (Dt.ty i = LType.Bd → (∀ u ∈ Dt.U i, ∀ y : ℤ, (Dt.h i : ℤ) ≤ y → y ≤ Dt.h i + Dt.sg l i + 1 → (u : k) ≠ (y : k)) ∧ (∀ u ∈ Dt.cloud i, ∀ y : ℤ, (Dt.h i : ℤ) - Dt.η i ≤ y → y ≤ Dt.h i → (u : k) ≠ (y : k)) ∧ (Dt.t : ℤ) ≤ Dt.wst i ∧ Dt.wst i ≤ Dt.η i) := by
  first | exact @GlobalTheory.WindowArith.windows | exact GlobalTheory.WindowArith.windows | (intros; apply GlobalTheory.WindowArith.windows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusion
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.CloseTw
open GlobalTheory.PhiGam.Close

theorem main : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  intro k _ l n m hl _ _ R D h w N₁ N₂ h₁ h₂ c₁ c₂ i
  classical
  have hex : ∀ i, ∃ a : ℕ, ∀ x ∈ N₁ i, vv k ^ a • x ∈ N₂ i := fun i => exists_pow (h₁ i).1 (h₂ i).2
  have hrec : ∀ i, Nat.find (hex (i - 1)) ≤ (Nat.find (hex i) + h i) / l := by
    intro i
    refine Nat.find_min' _ fun x hx => ?_
    refine key hl.out.pos R (D.φ i) (D.φ_semi i) (D.etale i) _ (h₂ _) _ x ?_
    have e1 : vv k ^ (w i) • D.φ i x ∈ N₁ i := by
      have := mem_sh_iff_smul_mem.1 ((c₁ i).1 (Submodule.subset_span ⟨x, hx, rfl⟩))
      rwa [neg_neg] at this
    have e2 := (c₂ i).2 (mem_sh_iff_exists.2 ⟨_, Nat.find_spec (hex i) _ e1, rfl⟩)
    have hv := vv_ne_zero k
    rw [smul_smul, smul_smul, ← zpow_natCast, ← zpow_add₀ hv, ← zpow_add₀ hv] at e2
    rw [← zpow_natCast]
    convert e2 using 3
    push_cast
    ring
  have hle := le_sg hl.out.one_lt h (fun i => Nat.find (hex i)) (fun i => by
    have := hrec (i + 1)
    simp only [add_sub_cancel_right] at this
    exact (Nat.mul_le_mul_left l this).trans (Nat.mul_div_le _ _)) i
  exact sh_le fun x hx => pow_smul_mem hle (Nat.find_spec (hex i) x hx)

end GlobalTheory.PhiGam.CloseTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamiliesShiftInclusionStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGamma_lattice_families_shift_inclusion : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (h : ZMod n → ℕ) (w : ZMod n → ℤ) (N₁ N₂ : Lats k n m), (∀ i, IsLat (N₁ i)) → (∀ i, IsLat (N₂ i)) → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₁ → CondAB D.φ w (fun i => (h i : ℤ) - w i) N₂ → ∀ i, sh (sg l h i) (N₁ i) ≤ N₂ i := by
  first | exact @GlobalTheory.PhiGam.CloseTw.main | exact GlobalTheory.PhiGam.CloseTw.main | (intros; apply GlobalTheory.PhiGam.CloseTw.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

noncomputable section

namespace GlobalTheory.Per.FilLetUnram

section Abstract

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem act_ι (g : G) (d : V ⊗[Qp] B) :
    actVdR PD ρ g (ιV PD (LL := LL) (V := V) d) = ιV PD (LL := LL) (V := V) (actVB PD ρ g d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [actVdR, ιV, actVB, PD.ι_comm]

theorem mul_ι (c : K₀) (d : V ⊗[Qp] B) :
    mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (algebraMap K₀ K c)
        (ιV PD (LL := LL) (V := V) d) =
      ιV PD (LL := LL) (V := V) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c d) := by
  induction d using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul v b => simp [mulVdR, ιV, mulVB, ← IsScalarTower.algebraMap_apply]

theorem ι_mem_DdRE (hs : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    {d : V ⊗[Qp] B} (hd : d ∈ DcrisL PD ρ (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))) :
    ιV PD (LL := LL) (V := V) d ∈ DdRE PD ρ τ := by
  obtain ⟨h1, h2⟩ := hd
  simp only [Dcris, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h1 h2
  constructor
  · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    rw [act_ι, h1 g]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero]
    intro c
    obtain ⟨c₀, rfl⟩ := hs c
    rw [mul_ι, h2 c₀, map_smul]
    rfl

theorem iSupIndep_DdRE : iSupIndep fun τ : K →ₐ[Qp] LL => DdRE PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K) (a : LL) => Module.End.eigenspace
      (mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K →ₐ[Qp] LL => (τ : K → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  have h2 := hx.2
  simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, LinearMap.smul_apply, sub_eq_zero] at h2
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact h2

end Abstract

theorem toDR_FilLet : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (τ : K →ₐ[Qp] LL) (a : ℤ), Function.Surjective (algebraMap K₀ K) → τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i → FildR PD T.ρ τ a = (FilCris PD T.ρ a ⊓ DcrisL PD T.ρ (W.emb i)).map (ιV PD (LL := LL) (V := T.V)) → GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.toDR (PD := PD) T (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.FilLet W T i τ a) = FildR PD T.ρ τ a := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ v n W T i τ a hs hτ hF
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
    have hxD : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
      ι_mem_DdRE PD T.ρ hs τ (by rw [hτ]; exact hx)
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 (Submodule.mem_comap.1 hx')
    have hzD : z ∈ DdRE PD T.ρ τ := by
      have : z = ιV PD (LL := LL) (V := T.V) x - y := by rw [← hyz]; abel
      rw [this]
      exact Submodule.sub_mem _ hxD hy.1
    have hz0 : z = 0 := (Submodule.disjoint_def.1 (iSupIndep_DdRE PD T.ρ τ)) z hzD hz
    rw [← hyz, hz0, add_zero]
    exact hy
  · intro y hy
    have hy' := hy
    rw [hF] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, ⟨hx.2, Submodule.mem_comap.2 (Submodule.mem_sup_left hy)⟩, rfl⟩

end GlobalTheory.Per.FilLetUnram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwist
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

namespace GlobalTheory.CyclotomicTowerSubgroupInclusions

variable {l : ℕ} [Fact l.Prime]

theorem unramified_subfield_le_Ks (K : FinExt l) (j : ℕ) : K0 K ≤ Ks K j := le_sup_left

theorem Ks_le_Kinf (K : FinExt l) (j : ℕ) : Ks K j ≤ Kinf K :=
  sup_le_sup_left (IntermediateField.adjoin.mono _ _ _ (fun _ hx => Exists.intro j hx)) _

theorem cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified (K : FinExt l) (j : ℕ) : Gj K j ≤ (K0 K).fixingSubgroup :=
  fun _ hg x => hg ⟨x.1, unramified_subfield_le_Ks K j x.2⟩

theorem Hinf_le_Gj (K : FinExt l) (j : ℕ) : Hinf K ≤ Gj K j :=
  fun _ hg x => hg ⟨x.1, Ks_le_Kinf K j x.2⟩

theorem mem_inC_iff (F : IntermediateField ℚ_[l] (Om l)) (y : PadicComplex l) :
    y ∈ inC F ↔ y ∈ F.toSubfield.map (algebraMap (Om l) (PadicComplex l)) := Iff.rfl

theorem algebraMap_mem_inC (F : IntermediateField ℚ_[l] (Om l)) (u : ℚ_[l]) :
    algebraMap ℚ_[l] (PadicComplex l) u ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) u, F.algebraMap_mem u, rfl⟩

theorem act_fix {act : GQ l →* (PadicComplex l ≃+* PadicComplex l)} (ha : IsActC act)
    {F : IntermediateField ℚ_[l] (Om l)} {g : GQ l} (hg : g ∈ F.fixingSubgroup)
    {y : PadicComplex l} (hy : y ∈ inC F) : act g y = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  have := hg ⟨x, hx⟩
  change g x = x at this
  simp only [ha.1, this]

theorem exists_scale (y : PadicComplex l) : ∃ n : ℕ, ‖(l : PadicComplex l) ^ n * y‖ ≤ 1 := by
  have hl : ‖(l : PadicComplex l)‖ < 1 := by
    have h1 : ‖algebraMap ℚ_[l] (PadicComplex l) (l : ℚ_[l])‖ = ‖(l : ℚ_[l])‖ := norm_algebraMap' _ _
    rw [map_natCast] at h1
    rw [h1]
    exact Padic.norm_p_lt_one
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hl).mul_const ‖y‖
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rwa [norm_mul, norm_pow]⟩

theorem invariants_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  intro l _ act χ ha hχ K j hj i y hy
  obtain ⟨hnorm, -, hker⟩ := GlobalTheory.T.cyclotomicCharacterPadic_basic_properties l χ hχ
  obtain ⟨⟨g, hg⟩, -⟩ := GlobalTheory.T.exists_cyclotomicTowerLevelGenerator_properties l act χ ha hχ K j hj
  obtain ⟨hdec, hdir, -, hmul, hact, -⟩ := GlobalTheory.T.tate_decomposition_completed_cyclotomic_integers l act χ ha hχ K j hj.1
  obtain ⟨n, hn⟩ := exists_scale y
  have hl0 : (l : PadicComplex l) ^ n ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  set z := (l : PadicComplex l) ^ n * y with hz
  have hzinv : ∀ σ ∈ Gj K j, chiC χ i σ * act σ z = z := by
    intro σ hσ
    rw [hz, map_mul, map_pow, map_natCast, mul_left_comm, hy σ hσ]
  have hzO : z ∈ Ohat K := by
    refine (GlobalTheory.T.cyclotomicTower_fixed_iff_mem_completedIntegers l act ha K z hn).mp fun h hh => ?_
    have h1 : χ h = 1 := (hker K h (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j (Hinf_le_Gj K j hh))).2.mp hh
    have h2 := hzinv h (Hinf_le_Gj K j hh)
    simpa [chiC, h1] using h2
  obtain ⟨a, haK, x, hx, hax⟩ := hdec z hzO
  set c := chiC χ i g with hc
  have hcK : c ∈ inC (Ks K j) := algebraMap_mem_inC _ _
  have hc1 : ‖c‖ = 1 := by
    rw [hc, chiC, norm_algebraMap', Units.val_zpow_eq_zpow_val, norm_zpow, hnorm, one_zpow]
  have hga : act g a = a := act_fix ha hg.1 haK.1
  have heq : c * (a + act g x) = a + x := by
    have := hzinv g hg.1
    rwa [hax, map_add, hga] at this
  have hX : x - c * act g x ∈ Xj K j :=
    (Xj K j).sub_mem hx (hmul c ⟨hcK, hc1.le⟩ _ (hact g (cyclotomicTowerLevelGaloisSubgroup_le_fixingUnramified K j hg.1) x hx))
  have hK : (c - 1) * a ∈ inC (Ks K j) := by
    rw [mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.sub_mem _ hcK (Subfield.one_mem _)) haK.1
  have h0 : (c - 1) * a = 0 := hdir _ hK _ hX 0 (by linear_combination heq)
  have hrho : 0 < rho1 l :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos) _
  have hx0 : x = 0 := by
    have h := (GlobalTheory.T.cyclotomic_tower_generator_matrix_perturbation l act χ ha hχ K j hj g hg 1 (fun _ => 1) (by
      intro a b
      rw [Subsingleton.elim a b, Matrix.one_apply_eq]
      refine ⟨?_, by simp⟩
      rw [mem_inC_iff]
      exact Subfield.one_mem _) (by intro a b; simpa using hrho) i).1 (fun _ => x) (fun _ => hx) (by
      funext b
      simp only [twAct, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul]
      linear_combination heq - h0)
    exact congrFun h 0
  rw [hx0, add_zero] at hax
  refine ⟨fun hi => ?_, fun _ => ?_⟩
  · have hv := GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt l j hj (χ g : ℚ_[l]) hg.2 i hi
    have hne : c - 1 ≠ 0 := by
      intro h
      have h2 : c - 1 = algebraMap ℚ_[l] (PadicComplex l) ((χ g : ℚ_[l]) ^ i - 1) := by
        rw [hc, chiC, Units.val_zpow_eq_zpow_val, map_sub, map_one]
      rw [h2, map_eq_zero] at h
      rw [h, norm_zero] at hv
      exact (zpow_pos (Nat.cast_pos.mpr (Fact.out : l.Prime).pos : (0 : ℝ) < l) _).ne hv
    have ha0 : a = 0 := (mul_eq_zero.mp h0).resolve_left hne
    rw [ha0, hz] at hax
    exact (mul_eq_zero.mp hax).resolve_left hl0
  · have : y = ((l : PadicComplex l) ^ n)⁻¹ * a := by
      rw [← hax, hz, inv_mul_cancel_left₀ hl0]
    rw [this, mem_inC_iff]
    exact Subfield.mul_mem _ (Subfield.inv_mem _ (Subfield.pow_mem _ (natCast_mem _ l) n)) haK.1

end GlobalTheory.CyclotomicTowerSubgroupInclusions
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateInvariantsCyclotomicTwistStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_invariants_cyclotomic_twist : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ j : ℕ, Lev l j → ∀ (i : ℤ) (y : PadicComplex l), (∀ g ∈ Gj K j, chiC χ i g * act g y = y) → (i ≠ 0 → y = 0) ∧ (i = 0 → y ∈ inC (Ks K j)) := by
  first | exact @GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist | exact GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist | (intros; apply GlobalTheory.CyclotomicTowerSubgroupInclusions.invariants_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjective
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.PhiGam.Img

section
variable {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V]
  [IsScalarTower k⟦X⟧ k⸨X⸩ V] {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W]
  [IsScalarTower k⟦X⟧ k⸨X⸩ W]

theorem map_sh (f : V →ₗ[k⸨X⸩] W) (a : ℤ) (N : Submodule k⟦X⟧ V) :
    (sh a N).map (f.restrictScalars k⟦X⟧) = sh a (N.map (f.restrictScalars k⟦X⟧)) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_sh_iff_exists.2 ⟨f y, ⟨y, hy, rfl⟩, (f.map_smul _ y).symm⟩
  · intro hx
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := mem_sh_iff_exists.1 hx
    exact ⟨_, mem_sh_iff_exists.2 ⟨y, hy, rfl⟩, f.map_smul _ y⟩

theorem isLat_map (f : V →ₗ[k⸨X⸩] W) (hf : Function.Surjective f) {N : Submodule k⟦X⟧ V} (h : IsLat N) :
    IsLat (N.map (f.restrictScalars k⟦X⟧)) := by
  refine ⟨h.1.map _, ?_⟩
  have : ((N.map (f.restrictScalars k⟦X⟧) : Submodule k⟦X⟧ W) : Set W) = f '' (N : Set V) := rfl
  rw [this, ← Submodule.map_span, h.2, Submodule.map_top, LinearMap.range_eq_top.2 hf]

theorem map_pull [Module k V] [Module k W] (f g : V →ₗ[k⸨X⸩] W) (φ : V →ₗ[k] V) (φ' : W →ₗ[k] W)
    (h : ∀ x, f (φ x) = φ' (g x)) (N : Submodule k⟦X⟧ V) :
    (pull φ N).map (f.restrictScalars k⟦X⟧) = pull φ' (N.map (g.restrictScalars k⟦X⟧)) := by
  rw [pull, pull, Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  exact Set.image_congr fun x _ => h x

end

theorem image_lattice :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  intro k _ l _ _ R n _ V _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ D D' f hf hφ hγ w w' N hN hAB hC N'
  refine ⟨fun i => isLat_map (f i) (hf i) (hN i), fun i => ?_, fun i => ?_⟩
  · simp only [N']
    rw [← map_pull (f i) (f (i - 1)) (D.φ i) (D'.φ i) (hφ i), ← map_sh, ← map_sh]
    exact ⟨Submodule.map_mono (hAB i).1, Submodule.map_mono (hAB i).2⟩
  · rintro _ ⟨x, hx, rfl⟩
    simp only [N']
    rw [← map_sh]
    refine ⟨_, hC i x hx, ?_⟩
    change f i _ = D'.γ i (f i x) - f i x
    rw [map_sub, hγ]

end GlobalTheory.PhiGam.Img
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PhiGammaLatticeFamilyImageOfSurjectiveStatement
open GlobalTheory.PhiGam
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective :
    ∀ {k : Type} [Field k] {l : ℕ} [Fact l.Prime] [CharP k l] (R : RingPG k l)
      {n : ℕ} [NeZero n]
      {V : Type} [AddCommGroup V] [Module k⸨X⸩ V] [Module k⟦X⟧ V] [Module k V]
      [IsScalarTower k⟦X⟧ k⸨X⸩ V] [IsScalarTower k k⸨X⸩ V] [IsScalarTower k k⟦X⟧ V]
      [FiniteDimensional k⸨X⸩ V]
      {W : Type} [AddCommGroup W] [Module k⸨X⸩ W] [Module k⟦X⟧ W] [Module k W]
      [IsScalarTower k⟦X⟧ k⸨X⸩ W] [IsScalarTower k k⸨X⸩ W] [IsScalarTower k k⟦X⟧ W]
      [FiniteDimensional k⸨X⸩ W] (D : ModPG R n V) (D' : ModPG R n W)
      (f : ZMod n → V →ₗ[k⸨X⸩] W),
      (∀ i, Function.Surjective (f i)) →
      (∀ i x, f i (D.φ i x) = D'.φ i (f (i - 1) x)) →
      (∀ i x, f i (D.γ i x) = D'.γ i (f i x)) →
      ∀ (w w' : ZMod n → ℤ) (N : ZMod n → Submodule k⟦X⟧ V),
        (∀ i, IsLat (N i)) → CondAB D.φ w w' N → (∀ i, CondC (D.γ i) (N i)) →
        (let N' := fun i => (N i).map ((f i).restrictScalars k⟦X⟧)
         (∀ i, IsLat (N' i)) ∧ CondAB D'.φ w w' N' ∧ ∀ i, CondC (D'.γ i) (N' i)) := by
  exact @_root_.GlobalTheory.PhiGam.Img.image_lattice
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbc
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem model_obj_and_abc : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  intro k G _ _ l n _ _ _ R F r Dt M A N h
  obtain ⟨B, Nb, A₁, j, p, hB, hj, hji, hp, hps, rfl⟩ := h
  have oB : F.Obj B := M.base_obj B Nb hB
  have o1 : F.Obj A₁ := F.obj_sub A₁ B j hj hji oB
  have oA : F.Obj A := F.obj_quot A₁ A p hp hps o1
  obtain ⟨h1, h2, h3⟩ := M.base_abc B Nb hB
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.phiGammaModule_saturation_theorem R (F.D B) (F.D A₁) (F.map A₁ B j)
    (F.map_inj A₁ B j o1 oB hj hji) (F.map_φ A₁ B j o1 oB hj) (F.map_γ A₁ B j o1 oB hj)
    Dt.w Dt.wst Nb h1 h2 h3
  exact ⟨oA, GlobalTheory.T.phiGammaLatticeFamily_image_of_surjective R (F.D A₁) (F.D A) (F.map A₁ A p)
    (F.map_surj A₁ A p o1 oA hp hps) (F.map_φ A₁ A p o1 oA hp) (F.map_γ A₁ A p o1 oA hp)
    Dt.w Dt.wst (F.pre A₁ B j Nb) s1 s2 s3⟩

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.obj_and_abc_of_model : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A : Ob k G) (N : Lats k n A.m), M.Model A N → F.Obj A ∧ ABC (F.D A) Dt.w Dt.wst N := by
  first | exact @GlobalTheory.Models.model_obj_and_abc | exact GlobalTheory.Models.model_obj_and_abc | (intros; apply GlobalTheory.Models.model_obj_and_abc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem ModTh.model_push_of_surjective {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l]
    [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (N : Lats k n A.m) (hp : IsHom A B p)
    (hs : Function.Surjective p) (hN : M.Model A N) : M.Model B (F.push A B p N) := by
  obtain ⟨C, Nb, A₁, j, q, hb, hj, hji, hq, hqs, rfl⟩ := hN
  have hC : F.Obj C := M.base_obj C Nb hb
  have h1 : F.Obj A₁ := F.obj_sub A₁ C j hj hji hC
  have hA : F.Obj A := F.obj_quot A₁ A q hq hqs h1
  have hB : F.Obj B := F.obj_quot A B p hp hs hA
  refine ⟨C, Nb, A₁, j, p ∘ₗ q, hb, hj, hji, fun g x => ?_, hs.comp hqs, ?_⟩
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, hq g x, hp g]
  · funext i
    simp only [DFun.push]
    rw [F.map_comp A₁ A B q p h1 hA hB hq hp i, ← Submodule.map_comp]
    rfl

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPtPrimitiveRoot
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_isPt_primitiveRoot {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ (ζ : ↥LL.1) (τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1), H.IsPt h i ζ τ ∧ IsPrimitiveRoot ζ (l ^ s) := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
    obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
    have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
      intro k
      induction k with
      | zero => simp
      | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
    have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
    have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
      rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
    have h3 := orderOf_eq_prime_pow h1 h2
    rw [← h3]
    exact IsPrimitiveRoot.orderOf _
  have hmem : P.ζQ s ∈ Ks K s :=
    (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ l ^ s = 1} ≤ Ks K s)
      (IntermediateField.subset_adjoin _ _ hprim.pow_eq_one)
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := Φ.comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (y : Om l) := fun _ => rfl
  refine ⟨τ ⟨P.ζQ s, hmem⟩, τ, ⟨?_, ?_⟩, ?_⟩
  · intro x y hxy
    apply Subtype.ext
    rw [hτ, hxy, hΦ]
  · intro y hy
    congr 1
    exact Subtype.ext hy
  · have h1 : IsPrimitiveRoot (⟨P.ζQ s, hmem⟩ : ↥(Ks K s)) (l ^ s) :=
      IsPrimitiveRoot.of_map_of_injective (f := (Ks K s).val) hprim (Ks K s).val.injective
    exact h1.map_of_injective τ.injective

end GlobalTheory
end
