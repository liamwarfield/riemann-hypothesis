module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiTrivOut
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DistinctWordsDistinctParameters
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormStepsLeviOntoSEnd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKu

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.Vanish Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ratLink_unique {x y : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hx : RatLink X x γ)
    (hy : RatLink X y γ) : x = y := by
  obtain ⟨M, -, h1, h2, h3⟩ := hx
  obtain ⟨N, -, k1, k2, k3⟩ := hy
  have hMN : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = N := by
    ext i j
    obtain ⟨w, hw⟩ : ∃ w, X.crd w = Pi.single j 1 :=
      ⟨Formalism.L2.SG.Pf.LatDictK.vOf X (Pi.single j 1), Formalism.L2.SG.Pf.LatDictK.crd_vOf X _⟩
    have e := (h3 w).symm.trans (k3 w)
    rw [hw] at e
    have := congrFun e i
    simpa [Matrix.mulVec_single_one] using this
  have hMN' : M = N := Units.ext hMN
  subst hMN'
  refine Prod.ext (funext fun v => ?_) ?_
  · exact Subtype.ext (Units.ext ((h1 v).trans (k1 v).symm))
  · exact Subtype.ext (Units.ext (h2.trans k2.symm))

variable {X} (TR : TypedRed X)

theorem levi_eq_one_of {a : X.B.I.Gf} (ga : Good X a)
    (hb : ∀ j, (X.B.I.fmat a - 1) *ᵥ X.bw j ∈ Mo X.B.I X.B.g (Set.range X.e0)) : levi TR a = 1 := by
  funext v
  apply Units.ext
  rw [levi_coe TR ga]
  ext i j
  have hbw : ∀ j, X.bw j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).1
  have hbwd : ∀ j, X.bwd j ∈ X.B.I.Lf := fun j => (X.vectorsInLattice.2.2 j).2
  have hI := hA_int X.B.I (hbwd i) (K_mv X.B.I ga.1.1 (hbw j))
  have hZ1 : ZMod' X.B.I X.B.g (hA X.B.I (X.bwd i) ((X.B.I.fmat a - 1) *ᵥ X.bw j)) :=
    Z_pair_Mo X (hbwd i) (by rintro _ ⟨b, rfl⟩; exact dual_beta_reference_congruence i b) _ (hb j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA_sub_right] at hZ1
  have hZ := Z_add X.B.I X.B.g hZ1 (X.bw_dual i j)
  rw [show hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - hA X.B.I (X.bwd i) (X.bw j) +
    (hA X.B.I (X.bwd i) (X.bw j) - if i = j then X.ew else 0) =
    hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j) - if i = j then X.ew else 0 by ring] at hZ
  show resT TR v (hA X.B.I (X.bwd i) (X.B.I.fmat a *ᵥ X.bw j)) = _
  rw [resT_of_mem TR v hI, res_of_Z_delta TR v hI (i = j) hZ, Pi.one_apply, Units.val_one, Matrix.one_apply]

theorem rep_split {u u' : D.what₂.Word} (Y : Formalism.L2.SG.Full.Full X) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ : Λ ∈ Y.what₂ u) (hΛ' : Λ' ∈ Y.what₂ u') (p q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ')
    (hpq : GRel X u u' (X.Fu u) (X.Fu u') Λ Λ' p q) :
    ∃ (n n' : (VS D).V ≃ₗ[D.host.E] (VS D).V) (xn xn' : X.B.I.GA),
      n ∈ NLam Λ (lf D (X.Fu u)) ∧ n' ∈ NLam Λ' (lf D (X.Fu u')) ∧ RatLink X xn n ∧ RatLink X xn' n' ∧
      q.1.2 = n * p.1.2 * n' ∧ q.1.1 = xn * p.1.1 * xn' := by
  obtain ⟨n, hn, n', hn', hq⟩ := hpq
  obtain ⟨xn, hxn⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hn.1.1
  obtain ⟨xn', hxn'⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n' hn'.1.1
  refine ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, ?_⟩
  have h1 : RatLink X q.1.1 q.1.2 := q.2.1
  have h2 : RatLink X (xn * p.1.1 * xn') (n * p.1.2 * n') := ratLink_mul X (ratLink_mul X hxn p.2.1) hxn'
  rw [← hq] at h2
  exact ratLink_unique X h1 h2

end Formalism.L2.SG.Pf.AmpIota

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.AmpIota

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem iotaRepC_holds : Formalism.L2.SG.Pf.SatGramRep.IotaRepC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', -, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, -⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, -⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have ga : Good X a := good_of_ncong X ha1.1 ⟨ha1.2.1, ha1.2.2.1⟩
  have ga' : Good X a' := good_of_ncong X ha1'.1 ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have gκ := good_of_ncong X hκK
    (adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X) hΛ hΛ' p hκK)
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group

  have hlev : ∀ (w : D.what₂.Word) (Lw : Submodule (𝓞 D.host.E) (VS D).V) (hh : Hfin X w) (m : X.B.I.GA)
      (nm : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X m nm → nm ∈ NLam Lw (lf D (X.Fu w)) →
      ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) ∈ X.B.I.Kset →
      Good X (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) →
      levi Y.TR (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) = 1 := by
    intro w Lw hh m nm hm hnm hK gA
    obtain ⟨C, hC⟩ := Formalism.L2.SG.Pf.exists_goodC X w
    have hN0 := Formalism.L2.SG.Pf.nLamNfin_holds D X w Lw m nm hm hnm
    have hN1 := (Formalism.L2.SG.PoincareInHH.Cut.nfinConj_holds X w hh⁻¹ m.2 hN0).1
    simp only [Subgroup.coe_inv, inv_inv] at hN1
    have e : ((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w) =
        (X.xu w)⁻¹ * ((hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf)) * X.xu w := by group
    have hK1 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) ∈ X.B.I.Kset := by
      have e2 : (hh : X.B.I.Gf)⁻¹ * m.2 * (hh : X.B.I.Gf) =
          X.xu w * (((hh : X.B.I.Gf) * X.xu w)⁻¹ * m.2 * ((hh : X.B.I.Gf) * X.xu w)) * (X.xu w)⁻¹ := by group
      rw [e2]
      exact K_mul X.B.I (K_mul X.B.I (X.xu_K w) hK) (K_inv X.B.I (X.xu_K w))
    refine levi_eq_one_of Y.TR gA (fun j => ?_)
    rw [e]
    exact Formalism.L2.SG.Pf.cong_b hC hN1 hK1 j
  have hla := hlev u Λ ((Y.cs u).h ((Y.cs u).base Λ)) xn n hxn hn ha1.1 ga
  have hla' := hlev u' Λ' ((Y.cs u').h ((Y.cs u').base Λ')) xn' n' hxn' hn' ha1'.1 ga'
  show levi Y.TR (kOf X u u' hb hb' q.1.1) = levi Y.TR (kOf X u u' hb hb' p.1.1)
  rw [hk, levi_mul Y.TR (good_mul X ga gκ) ga', levi_mul Y.TR ga gκ, hla, hla', one_mul, mul_one]

theorem ampRepNC_holds : Formalism.L2.SG.Pf.SatGramRep.AmpRepNC := by
  intro D X Y u u' Λ Λ' hΛ hΛ' p q hpq Ωp Ωq hΩp hΩq _
  obtain ⟨n, n', xn, xn', hn, hn', hxn, hxn', hq, hq1⟩ := rep_split Y hΛ hΛ' p q hpq
  have hbl : (Y.cs u).lamOf ((Y.cs u).base Λ) = Λ := (Y.cs u).base_lam Λ hΛ
  have hbl' : (Y.cs u').lamOf ((Y.cs u').base Λ') = Λ' := (Y.cs u').base_lam Λ' hΛ'
  obtain ⟨ha1, -, ha3⟩ := nilradical_conj_level' D X Y u ((Y.cs u).base Λ) xn n (by rw [hbl]; exact hn) hxn
  obtain ⟨ha1', -, ha3'⟩ := nilradical_conj_level' D X Y u' ((Y.cs u').base Λ') xn' n' (by rw [hbl']; exact hn') hxn'
  set hb : X.B.I.Gf := ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf)
  set hb' : X.B.I.Gf := ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf)
  set a := (hb * X.xu u)⁻¹ * xn.2 * (hb * X.xu u) with hadef
  set a' := (hb' * X.xu u')⁻¹ * xn'.2 * (hb' * X.xu u') with ha'def
  have hκK := termK_car (Y.cs u) (Y.cs u') hΛ hΛ' p
  have hκN := adm_norm_of_carrier (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') (Formalism.L2.SG.Pf.modGAt X)
    hΛ hΛ' p hκK
  have hk : kOf X u u' hb hb' q.1.1 = a * kOf X u u' hb hb' p.1.1 * a' := by
    rw [hq1, hadef, ha'def]; simp only [kOf, Prod.snd_mul]; group
  have haN : NCong X a := ⟨ha1.2.1, ha1.2.2.1⟩
  have haN' : NCong X a' := ⟨ha1'.2.1, ha1'.2.2.1⟩
  have hχ : chiN X (kOf X u u' hb hb' q.1.1) =
      X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 := by
    rw [hk, Formalism.L2.SG.Pf.ChiNMul.chiN_mul X (K_mul X.B.I ha1.1 hκK) (ncong_mul X ha1.1 haN hκN) haN',
      Formalism.L2.SG.Pf.ChiNMul.chiN_mul X ha1.1 haN hκN]
    have e1 := (ha3 1 Y.hK.1).1
    have e2 := (ha3' 1 Y.hK.1).1
    rw [mul_one, Formalism.L2.SG.Pf.ChiNMul.chiN_one, mul_one] at e1 e2
    rw [e1, e2]
  have hΩq' : Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (n * p.1.2 * n')) Ωq := by
    rw [← hq]; exact hΩq
  have hoo := oo_rel Formalism.L2.SG.Pf.nLamNinf_holds chiTrivialC_outright Y hΛ hΛ' p hn hn' hxn hxn' hΩp hΩq'
  have hP1 := Formalism.L2.SG.Pf.psiProd_all D X u xn (ratLink_mem X hxn)
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u _ xn n hxn hn) (Formalism.L2.SG.Pf.nLamNfin_holds D X u _ xn n hxn hn)
  have hP2 := Formalism.L2.SG.Pf.psiProd_all D X u' xn' (ratLink_mem X hxn')
    (Formalism.L2.SG.Pf.nLamNinf_holds D X u' _ xn' n' hxn' hn') (Formalism.L2.SG.Pf.nLamNfin_holds D X u' _ xn' n' hxn' hn')
  rw [hχ, hq1]
  rw [hoo, smul_smul]
  have hc : X.psiFinU u xn.2 * chiN X (kOf X u u' hb hb' p.1.1) * X.psiFinU u' xn'.2 *
      (X.psiInfU u xn.1 * X.psiInfU u' xn'.1) = chiN X (kOf X u u' hb hb' p.1.1) := by
    linear_combination (chiN X (kOf X u u' hb hb' p.1.1)) *
      (X.psiInfU u xn.1 * X.psiFinU u xn.2 * hP2 + hP1)
  rw [hc]

end Formalism.L2.SG.Pf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabCoverPfLam
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.KExpCut
  Formalism.L2.SG.Full Formalism.L2.SG.Pf.Slab Formalism.L2.SG.Pf.Vanish2
open Matrix

namespace Formalism.L2.SG.Pf.SlabCoverPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_ker_mat {E : Type*} [Field E] {n : ℕ} (W : Submodule E (Fin n → E)) :
    ∃ (k : ℕ) (B : Matrix (Fin k) (Fin n) E), ∀ w, B *ᵥ w = 0 ↔ w ∈ W := by
  classical
  let b := Module.finBasis E ((Fin n → E) ⧸ W)
  refine ⟨Module.finrank E ((Fin n → E) ⧸ W), Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1)),
    fun w => ?_⟩
  have key : ∀ i, ((Matrix.of fun i j => b.coord i (W.mkQ (Pi.single j 1))) *ᵥ w) i =
      b.coord i (W.mkQ w) := by
    intro i
    conv_rhs => rw [show w = ∑ j, w j • Pi.single j 1 by
      funext x; simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
  constructor
  · intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    apply b.repr.injective
    ext i
    have e := congrFun h i
    rw [key] at e
    simpa using e
  · intro hw
    funext i
    rw [key]
    simp [(Submodule.Quotient.mk_eq_zero W).2 hw]

theorem rv_desc {D : D7} (X : HidaSetting D) (v : InfinitePlace X.B.I.F) (T : Set (Fin X.B.I.n → X.B.I.E))
    (w : Fin X.B.I.n → X.B.I.E) (h : rv X.B.I v w ∈ Submodule.span ℂ (rv X.B.I v '' T)) :
    w ∈ Submodule.span X.B.I.E T := by
  classical
  obtain ⟨k, B, hB⟩ := exists_ker_mat (Submodule.span X.B.I.E T)
  rw [← hB w]
  have hφ : ∀ y : Fin X.B.I.n → X.B.I.E,
      (B.map (X.B.I.φ v)) *ᵥ (fun i => X.B.I.φ v (y i)) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hrv : ∀ y, (fun i => X.B.I.φ v (y i)) = X.B.I.P v *ᵥ rv X.B.I v y := by
    intro y
    rw [rv, Matrix.mulVec_mulVec, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.one_mulVec]
  let M : (Fin X.B.I.n → ℂ) →ₗ[ℂ] (Fin k → ℂ) := Matrix.mulVecLin (B.map (X.B.I.φ v) * X.B.I.P v)
  have hM : ∀ y, M (rv X.B.I v y) = fun i => X.B.I.φ v ((B *ᵥ y) i) := by
    intro y
    simp only [M, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← hrv, hφ]
  have hT : ∀ t ∈ T, M (rv X.B.I v t) = 0 := by
    intro t ht
    rw [hM, (hB t).2 (Submodule.subset_span ht)]
    funext i
    simp
  have hle : Submodule.span ℂ (rv X.B.I v '' T) ≤ LinearMap.ker M := by
    rw [Submodule.span_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hT t ht
  have hw0 : M (rv X.B.I v w) = 0 := hle h
  rw [hM] at hw0
  funext i
  have e := congrFun hw0 i
  exact (map_eq_zero_iff _ (X.B.I.φ v).injective).1 e

def toVHom {D : D7} (X : HidaSetting D) : (Fin X.B.I.n → X.B.I.E) →+ (VS D).V where
  toFun := toV X
  map_zero' := by
    have h := toV_add X 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  map_add' := toV_add X

theorem toV_span {D : D7} (X : HidaSetting D) {S : Set (Fin D.R.rS)} {w : Fin X.B.I.n → X.B.I.E}
    (hw : w ∈ Submodule.span X.B.I.E (X.eR '' S)) : toV X w ∈ Submodule.span D.host.E (X.eX '' S) := by
  induction hw using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    show toV X (X.crd (X.eX a)) ∈ _
    rw [toV_crd]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  | zero =>
    rw [show toV X 0 = 0 from (toVHom X).map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [toV_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [toV_smul]
    exact Submodule.smul_mem _ _ hx

theorem nilradical_rational_lattice : NRatLam := by
  intro D X Y u ρ ν hKL hν h1 _ hK2
  obtain ⟨γ, hγU, hγinf, hγfin⟩ := hν

  have hrvg : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y) =
        uMat (ν.1 v) *ᵥ rv X.B.I v y := by
    intro v y
    rw [hγinf v, rv, rv]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Formalism.MainNotions.LeviCoordinates.rrg_P_mul_inv, Matrix.mul_one]
    rw [← Matrix.mulVec_mulVec]
    congr 1
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  have hsub : ∀ (v : InfinitePlace X.B.I.F) (y : Fin X.B.I.n → X.B.I.E),
      (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v y =
        rv X.B.I v ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ y - y) := by
    intro v y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← hrvg]
    exact (map_sub (Formalism.L2.SG.Pf.Level.rvHom X v) _ _).symm

  have hdesc : ∀ (S : Set (Fin D.R.rS)) (x : (VS D).V),
      (∀ v, (uMat (ν.1 v) - 1) *ᵥ rv X.B.I v (X.crd x) ∈
        Submodule.span ℂ ((fun a => rv X.B.I v (X.eR a)) '' S)) →
      matEC X γ x - x ∈ Submodule.span D.host.E (X.eX '' S) := by
    intro S x hx
    obtain ⟨v⟩ : Nonempty (InfinitePlace X.B.I.F) := inferInstance
    have h := hx v
    rw [hsub, ← Set.image_image (fun w => rv X.B.I v w) X.eR S] at h
    have hw := rv_desc X v _ _ h
    have e : matEC X γ x - x =
        toV X ((γ : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd x - X.crd x) := by
      rw [← matE_crdC X γ x, ← crd_sub', toV_crd]
    rw [e]
    exact toV_span X hw
  show ∃ (x : X.B.I.GA) (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x n ∧ ν.1 = x.1 ∧
    n ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))
  refine ⟨ν, matEC X γ, ⟨γ, hγU, hγinf, hγfin, fun y => matE_crdC X γ y⟩, rfl, ?_⟩
  show _ ∧ _ ∧ _
  refine ⟨?_, ?_, ?_⟩
  · rw [isAutLam_iff]
    refine ⟨fun x y => matE_isomC X γ hγU x y, fun y => ?_⟩
    rw [(Y.cs u).lat_eq ρ (matEC X γ y), (Y.cs u).lat_eq ρ y, matE_inclC, ← hγfin, Matrix.mulVec_mulVec]
    have hk : ∀ w, w ∈ X.B.I.Lf ↔ X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 *
        (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *ᵥ w ∈ X.B.I.Lf := hKL.2.1 _ hK2
    have e : X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat ν.2 =
        X.B.I.fmat ((((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ * ν.2 * (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)) *
          X.B.I.fmat (((Y.cs u).h ρ : X.B.I.Gf) * X.xu u)⁻¹ := by
      simp [AutInst.fmat, Matrix.mul_assoc]
    rw [e, ← Matrix.mulVec_mulVec]
    exact (hk _).symm
  · intro j x hx
    change x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j + 1}) at hx
    change matEC X γ x - x ∈ Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < j})
    rw [X.Fu_e u] at hx ⊢
    let Lm : (VS D).V →ₗ[D.host.E] (VS D).V :=
      (matEC X γ : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id
    have hL : ∀ y, Lm y = matEC X γ y - y := fun y => rfl
    rw [← hL]
    refine (Submodule.span_le (p := (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm)).2 ?_ hx
    rintro _ ⟨i, hi, rfl⟩
    show X.eX i ∈ (Submodule.span D.host.E (X.eX '' {i | i.1 < j})).comap Lm
    rw [Submodule.mem_comap, hL]
    refine Submodule.span_mono (Set.image_mono fun b hb => ?_)
      (hdesc {b | b.1 < i.1} (X.eX i) fun v => (h1 v).1.1 i)
    simp only [Set.mem_setOf_eq] at hb hi ⊢
    omega
  · intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    have hx' : ∀ a, (VS D).hT (X.eX a) x = 0 := by
      intro a
      refine hx (X.eX a) ?_
      change X.eX a ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
      rw [X.Fu_e u]
      exact Submodule.subset_span ⟨a, rfl⟩
    change matEC X γ x - x ∈ Submodule.span D.host.E (Set.range (X.Fu u).e)
    rw [X.Fu_e u]
    have hsp : Submodule.span D.host.E (X.eX '' {b : Fin D.R.rS | b.1 < D.R.rS}) =
        Submodule.span D.host.E (Set.range X.eX) := by
      congr 1
      ext y
      simp
    rw [← hsp]
    refine hdesc _ x fun v => (h1 v).2 _ fun a => ?_
    show hJ (X.B.I.ε v) (rv X.B.I v (X.crd (X.eX a))) (rv X.B.I v (X.crd x)) = 0
    rw [hJ_crd, hx' a, map_zero]

end Formalism.L2.SG.Pf.SlabCoverPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetKey
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

def IdMeetKeyC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), NeatKu X u Y.hK →
    ∀ (ρ ρ' : (Y.cs u).Cl) (t : GTerm X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u)), t.isId →
      Meets (Y.cs u) (Y.cs u) t ρ ρ' →
        ρ = ρ' ∧ t.lin ∈ NLam ((Y.cs u).lamOf ρ) (lf D (X.Fu u))

def VolColC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (ρ : (Y.cs u).Cl) (Ω : Set X.B.I.Ginf),
    IsSFund X.B.I (Formalism.L2.SG.TermOp.KExpCut.NOcol (X.Fu u) (Y.cs u) ρ) Ω → X.muN u Ω = X.muN u (Y.FN u)

end Formalism.L2.SG.Pf.IdMeet
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealFramesCharacters
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Matrix

namespace Formalism.L2.SG.RealObj.RealFramesCharacters

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem fam_rv (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) (a : Fin (D.R.rS + 1)) :
    fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a = rv X.B.I v (X.crd ((X.Fu u).fvec a)) := by
  induction a using Fin.lastCases with
  | last => simp only [fam, Fin.snoc_last, FlagG.fvec, X.flagZVector u]; rfl
  | cast b => simp only [fam, Fin.snoc_castSucc, FlagG.fvec, X.Fu_e u]; rfl

theorem rv_sum (v : InfinitePlace X.B.I.F) {ι : Type} (t : Finset ι) (c : ι → X.B.I.E) (y : ι → Fin X.B.I.n → X.B.I.E) :
    rv X.B.I v (∑ i ∈ t, c i • y i) = ∑ i ∈ t, X.B.I.φ v (c i) • rv X.B.I v (y i) := by
  unfold rv
  have h : (fun j => X.B.I.φ v ((∑ i ∈ t, c i • y i) j)) =
      ∑ i ∈ t, X.B.I.φ v (c i) • (fun j => X.B.I.φ v (y i j)) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, map_sum, smul_eq_mul, map_mul]
  rw [h, Matrix.mulVec_sum]
  congr 1
  funext i
  rw [Matrix.mulVec_smul]

theorem real_frame (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) (v : InfinitePlace X.B.I.F)
    (a : Fin (D.R.rS + 1)) :
    uMat (x.1 v) *ᵥ fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) a =
      ∑ c, X.B.I.φ v (X.ιE.symm (un c a)) • fam (fun b => rv X.B.I v (X.eR b)) (rv X.B.I v (X.zR u)) c := by
  obtain ⟨M, -, hv, -, hcrd⟩ := hRL
  simp only [fam_rv]
  rw [hv v, Formalism.L2.SG.Pf.rv_mulVec, ← hcrd, hun, Formalism.L2.SG.NormCut.crd_sum']
  simp only [Formalism.L2.SG.NormCut.crd_smul']
  rw [rv_sum]

theorem psiInf_rat (u : D.what₂.Word) {x : X.B.I.GA} {n : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    (hRL : Formalism.L2.SG.TermOp.RatLink X x n) (un : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E)
    (hun : ∀ b, n ((X.Fu u).fvec b) = ∑ c, un c b • (X.Fu u).fvec c) :
    X.psiInfU u x.1 = Formalism.L2.SG.PairVal.psiInf X.B.g (Formalism.L2.SG.PairVal.sgUp un) := by
  refine FormRegularity.psi_of_frame X u x.1 (fun v => (un.map (fun t => X.B.I.φ v (X.ιE.symm t)))ᵀ)
    (fun v a => by simpa [Matrix.transpose_apply, Matrix.map_apply] using real_frame X u hRL un hun v a) _ fun v => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.transpose_apply, Matrix.map_apply, FormRegularity.sgUp_eq, map_sum, star_sum, ← Finset.sum_add_distrib]

end Formalism.L2.SG.RealObj.RealFramesCharacters
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabMajPtPfSupp
noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem term_supp {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    ∃ (h : Hfin X u') (κ : X.B.I.Gf), κ ∈ X.K2 ∧
      t.pt.2⁻¹ * Formalism.L2.SG.Pf.Slab.aB Y u t.lam = (h : X.B.I.Gf) * X.xu u' * κ := by
  have hTF := Full.frameTie (X := X) u u'
  have hKk := Formalism.L2.SG.Closed.TermK_holds (F0 := X.Fu u) (F0' := X.Fu u') (Y.cs u) (Y.cs u') t
  have hNk := Formalism.L2.SG.Closed.AdmN_holds (Y.cs u) (Y.cs u') hTF t
  have hGk := Formalism.L2.SG.Closed.AdmPar_holds (Y.cs u) (Y.cs u') hTF t
  obtain ⟨h, hc, -, hlev⟩ := Formalism.L2.SG.Pf.NormSteps.levi_onto_reduction Y.TR (Y.cs u')
    ⟨t.lam', t.mem'⟩
    (levi Y.TR (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf)
      ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt))⁻¹
  have hNc := Formalism.L2.SG.NormCut.ncong_colDiff u' _ _ hc
  have hGc := Formalism.L2.SG.NormCut.good_of_ncong X hc hNc
  have hKkc := Formalism.L2.SG.Pf.unitaryCongruence.K_mul X.B.I hKk hc
  have hNkc := Formalism.L2.SG.NormCut.ncong_mul X hKk hNk hNc
  have hGkc := Formalism.L2.SG.NormCut.good_mul X hGk hGc
  have hlevkc := Formalism.L2.SG.NormCut.levi_mul Y.TR hGk hGc
  rw [hlev, mul_inv_cancel] at hlevkc
  have hK2 := Formalism.L2.SG.NormCut.mem_level_of_unitriangular Y.TR hGkc hNkc (fun v => by
    rw [hlevkc, Pi.one_apply]
    exact Formalism.L2.SG.GGMirabolic.isUni_one)
  refine ⟨h, _, Y.hK.2.2.1 _ hK2, ?_⟩
  simp only [Formalism.L2.SG.Pf.Slab.aB, kOf, Formalism.L2.SG.Pf.NormSteps.colDS]
  group

end Formalism.L2.SG.Pf.SlabMajPt
end
end

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.TermOp Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.SlabMajPt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D}

theorem col_val (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (T : Cu X w hK) (ξ : X.Vpi w) (γ : Gam X w) (x : Hfin X w)
    (κ : Ku X w hK) :
    (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, iotaF X w γ * x * (κ : Hfin X w)) =
      ((psiK X w hK κ : ℂˣ) : ℂ) *
        (T : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) (piRep X w (iotaI X w γ)⁻¹ ξ) (1, x) := by
  obtain ⟨hF, hE⟩ := T.2
  obtain ⟨hL, hR⟩ := hF ξ
  have e1 : ((1 : Hinf X w), iotaF X w γ * x * (κ : Hfin X w)) =
      ((1 : Hinf X w), iotaF X w γ * x) * ((1 : Hinf X w), (κ : Hfin X w)) := by simp
  have e2 : ((1 : Hinf X w), iotaF X w γ * x) = (iotaI X w γ, iotaF X w γ) * ((iotaI X w γ)⁻¹, x) := by simp
  have e3 : ((iotaI X w γ)⁻¹, x) = ((1 : Hinf X w), x) * ((iotaI X w γ)⁻¹, (1 : Hfin X w)) := by simp
  rw [e1, hR, e2, hL, e3, ← hE]

theorem norm_psiK (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (κ : Ku X w hK) : ‖((psiK X w hK κ : ℂˣ) : ℂ)‖ = 1 :=
  hK.2.2.2.2 _ κ.2

theorem col_lower (Y : Full X) (w : D.what₂.Word) :
    ∃ (n : ℕ) (T : Fin n → Cu X w Y.hK), ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
  have hst : Formalism.L2.SG.ColsDim.StabTriv (iotaF X w) (Ku X w Y.hK) :=
    Formalism.L2.SG.PoincareInHH.Cut.neatKu_of_gamUnipKu X w Y.hK (Formalism.L2.SG.PoincareInHH.Cut.latOfLattice_holds X w)
      (Formalism.L2.SG.PoincareInHH.Cut.gamUnipKu_holds X w Y.hK)
  have hfin : Finite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK)) := by
    refine Finite.of_surjective
      (fun ρ : (Y.cs w).Cl => DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) ((Y.cs w).h ρ)) ?_
    intro c
    induction c using Quotient.inductionOn' with
    | h g =>
      obtain ⟨ρ, ⟨γ, κ, hg⟩, _⟩ := Y.colReps w g
      refine ⟨ρ, ?_⟩
      show DoubleCoset.mk _ _ _ = DoubleCoset.mk _ _ g
      rw [DoubleCoset.eq]
      exact ⟨iotaF X w γ, ⟨γ, rfl⟩, κ, κ.2, hg⟩
  have := Fintype.ofFinite (Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK))
  obtain ⟨e, he⟩ := Formalism.L2.SG.ColsDim.columns_decomposition (Gam X w) (Hinf X w) (Hfin X w) ℂ (X.Vpi w) (iotaI X w)
    (iotaF X w) (Ku X w Y.hK) (psiK X w Y.hK) (piRep X w) (fun c => c.out) (fun c => DoubleCoset.out_eq' c) hst
  obtain ⟨b, -⟩ : ∃ b : OrthonormalBasis (Fin (Module.finrank ℂ (X.Vpi w))) ℂ (X.Vpi w), True :=
    ⟨stdOrthonormalBasis ℂ (X.Vpi w), trivial⟩
  let ι := Formalism.L2.SG.ColsDim.Classes (iotaF X w) (Ku X w Y.hK) × Fin (Module.finrank ℂ (X.Vpi w))
  let f : ι → Cu X w Y.hK := fun p => e.symm (fun c => if c = p.1 then innerₛₗ ℂ (b p.2) else 0)
  have hf : ∀ p ξ, (f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, p.1.out) = inner ℂ (b p.2) ξ := by
    intro p ξ
    rw [← he]
    simp only [LinearEquiv.apply_symm_apply]
    rfl
  refine ⟨Fintype.card ι, fun i => f ((Fintype.equivFin ι).symm i), fun ξ h => ?_⟩
  obtain ⟨c, hc⟩ : ∃ c, c = DoubleCoset.mk (iotaF X w).range (Ku X w Y.hK) h := ⟨_, rfl⟩
  obtain ⟨g, ⟨γ, rfl⟩, κ, hκ, hh⟩ := (@DoubleCoset.eq _ _ _ _ c.out h).1 (by rw [DoubleCoset.out_eq', hc])
  obtain ⟨ξ', hξ'⟩ : ∃ ξ', ξ' = piRep X w (iotaI X w γ)⁻¹ ξ := ⟨_, rfl⟩
  have hn : ‖ξ'‖ = ‖ξ‖ := by
    have h2 : inner ℂ ξ' ξ' = inner ℂ ξ ξ := by
      rw [hξ']
      exact (X.piU_rep w).2.2.1 _ (hinf_le_sinf X w _ ((iotaI X w γ)⁻¹).2) ξ ξ
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ) ξ, h2]
  have hval : ∀ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ = ‖inner ℂ (b j) ξ'‖ₑ := by
    intro j
    rw [hh, col_val Y.hK w (f (c, j)) ξ γ c.out ⟨κ, hκ⟩, ← hξ', hf (c, j) ξ', enorm_mul,
      ← ofReal_norm (((psiK X w Y.hK ⟨κ, hκ⟩ : ℂˣ) : ℂ)), norm_psiK, ENNReal.ofReal_one, one_mul]
  calc ‖ξ‖ₑ = ‖ξ'‖ₑ := by rw [← ofReal_norm, ← ofReal_norm, hn]
    _ = ‖∑ j, inner ℂ (b j) ξ' • b j‖ₑ := by rw [b.sum_repr']
    _ ≤ ∑ j, ‖inner ℂ (b j) ξ' • b j‖ₑ := enorm_sum_le _ _
    _ = ∑ j, ‖inner ℂ (b j) ξ'‖ₑ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [enorm_smul, ← ofReal_norm (b j), b.orthonormal.1 j, ENNReal.ofReal_one, mul_one]
    _ = ∑ j, ‖(f (c, j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        Finset.sum_congr rfl fun j _ => (hval j).symm
    _ ≤ ∑ p : ι, ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ := by
        rw [Fintype.sum_prod_type]
        exact Finset.single_le_sum (f := fun c' => ∑ j, ‖(f (c', j) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
          (fun _ _ => bot_le) (Finset.mem_univ c)
    _ = ∑ i, ‖(f ((Fintype.equivFin ι).symm i) : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ :=
        (Equiv.sum_comp (Fintype.equivFin ι).symm
          (fun p => ‖(f p : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)).symm

theorem ph_lower (Y : Full X) (w : D.what₂.Word) {n : ℕ} (T : Fin n → Cu X w Y.hK)
    (hT : ∀ (ξ : X.Vpi w) (h : Hfin X w),
      ‖ξ‖ₑ ≤ ∑ i, ‖(T i : X.Vpi w →ₗ[ℂ] (Hinf X w × Hfin X w → ℂ)) ξ (1, h)‖ₑ)
    (x : X.B.I.Ginf) (h : Hfin X w) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    ‖X.Wu w x‖ₑ ≤ ∑ i, ‖Ph X w Y.hK (T i) (x, (h : X.B.I.Gf) * X.xu w * k)‖ₑ := by
  refine (hT (X.Wu w x) h).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [Formalism.L2.SG.Pf.RegroupPf.ph_col Y.hK (Formalism.L2.SG.Pf.phWellDef_holds X w) (T i) x h k hk, enorm_mul,
    ← ofReal_norm (X.chi2 k), Y.hK.2.2.2.2 k hk, ENNReal.ofReal_one, one_mul]

theorem pointwise_majorant_by_columns : Formalism.L2.SG.Pf.Slab.MajPtC := by
  intro D X Y u u'
  obtain ⟨n, T, hT⟩ := col_lower Y u
  obtain ⟨n', T', hT'⟩ := col_lower Y u'
  refine ⟨n, n', T, T', 1, ENNReal.one_ne_top, fun t x => ?_⟩
  obtain ⟨h, κ, hκ, he⟩ := term_supp Y u u' t
  have h1 := ph_lower Y u T hT x ((Y.cs u).h ((Y.cs u).base t.lam)) 1 Y.hK.1
  have h2 := ph_lower Y u' T' hT' (t.pt.1⁻¹ * x) h κ hκ
  have hb : t.pt⁻¹ * (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) = (t.pt.1⁻¹ * x, (h : X.B.I.Gf) * X.xu u' * κ) :=
    Prod.ext rfl he
  have ha : (x, Formalism.L2.SG.Pf.Slab.aB Y u t.lam) =
      (x, ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) * X.xu u * 1) := by
    rw [mul_one]; rfl
  rw [hb, ha, one_mul]
  exact (mul_le_mul' h1 h2).trans_eq (Finset.sum_mul_sum _ _ _ _)

end Formalism.L2.SG.Pf.SlabMajPt
end
end
