module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ContinuousOnThetaFrameValueHolomorphicFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdapted
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.AdaptedPeriods


set_option maxHeartbeats 1000000 in
theorem exists_adapted (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ)
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1))
    (y : FrPt Xo c (CAt σ)) (k : Fin F.n) (P : (F.Di k).La →+ (Fin g → ℂ))
    (hP : IsPeriod (F.Di k) (fun j => Formalism.L2.Pj.relab c σ (e j).1) P) (hy : F.u k P = y.x) :
    ∃ (w : Fin g → Fin g → ℂ) (V : Matrix (Fin g) (Fin g) ℂ) (P' : (F.Di k).La →+ (Fin g → ℂ)),
      (∀ j, IsDerivAt0 (fun z => (F.ex k P z).left) (w j) (y.u (e j).1 (e j).2)) ∧
      (∀ j, V *ᵥ w j = Pi.single j 1) ∧ (∀ a, P' a = V *ᵥ P a) ∧
      IsPeriod (F.Di k) (fun j => Formalism.L2.Pj.relab c σ (e j).1) P' ∧ y.x = F.u k P' ∧
      ∀ τ (i : Fin (Dw.mult τ)),
        IsDerivAt0 (fun z => (F.ex k P' z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) (y.u τ i) := by
  classical
  obtain ⟨x, hxs, u, htan, heig, hbas, s, hgen⟩ := y
  dsimp only at hy ⊢
  subst hy
  have hT := GlobalTheory.isDerivAt0_ex_isTanAt _ _ _ _ _ _ _ _ F k P hP
  have hw0 : ∀ p : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)),
      ∃ w, IsDerivAt0 (fun z => (F.ex k P z).left) w (u p.1 p.2) :=
    fun p => (hT.2.2 _ (htan p.1 p.2)).exists
  choose wp hwp using hw0
  have hblk : ∀ j, ∃ a : Fin (Dw.mult (e j).1) → ℂ,
      ∑ i, a i • wp (e (e.symm ⟨(e j).1, i⟩)) = Pi.single j 1 := by
    intro j
    obtain ⟨d, hd, -⟩ := hT.2.1 (Pi.single j 1)
    have hdt := hT.1 _ _ hd
    have hde := (GlobalTheory.isEigAt_iff_of_isDerivAt0 _ _ _ _ _ _ _ _ _ F k P hP (Pi.single j 1) d (e j).1 hd).2 (by
      intro j' hj'
      rw [Pi.single_apply] at hj'
      split_ifs at hj' with hjj
      · rw [hjj]
      · exact absurd rfl hj')
    obtain ⟨a, ha, -⟩ := hbas (e j).1 d hdt hde
    refine ⟨a, ?_⟩
    have hc := (GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 _ _ _ _ _ _ _ _ F k P hP (Dw.mult (e j).1) (u (e j).1)
      (fun i => wp (e (e.symm ⟨(e j).1, i⟩))) (fun i => by simpa using hwp ⟨(e j).1, i⟩) a d).1 ha
    exact (hT.2.2 d hdt).unique hc hd
  obtain ⟨V, hVdet, hVblk, hVw⟩ := GlobalTheory.CoverFrame.exists_inverse_block e (fun j => wp (e j)) hblk
  obtain ⟨P', hP', hP'V⟩ := GlobalTheory.PeriodLin.exists_period_mulVec _ _ _ _ _ P V hP hVdet
    (fun j j' h => congrArg (Formalism.L2.Pj.relab c σ) (hVblk j j' h))
  have hS : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (s : Y ≃ₗ[ℤ] Y) (n M : ℕ),
      0 < n → s ^ n = 1 → 3 ≤ M → (∀ y, ∃ z, s y = y + M • z) → s = 1 := by
    intro Y _ _ _ s n M hn hs hM h
    have h1 : (s : Module.End ℤ Y) ^ n = 1 := by
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun t : Y ≃ₗ[ℤ] Y => t v) hs
      simp only [LinearEquiv.coe_pow] at hv
      first
        | rw [Module.End.coe_pow]
        | rw [LinearMap.coe_pow]
      simpa using hv
    have h2 := GlobalTheory.end_eq_one_of_pow_eq_one_of_congr Y (s : Module.End ℤ Y) n M hn h1 hM h
    exact LinearEquiv.ext fun v => by simpa using LinearMap.congr_fun h2 v
  obtain ⟨-, hu, hex⟩ := GlobalTheory.FamRigid.ex_eq_of_level_group hS _ _ _ _ _ _ _ _ F k P P'
    (LinearEquiv.refl _ _) V hP hP' (fun a b => rfl) (fun a _ => ⟨0, by simp⟩) (fun a => ⟨0, by simp⟩)
    (fun a => hP'V a)
  have hD := GlobalTheory.ExpChain.isDerivAt0_ex_iff _ _ _ _ _ _ _ _ F k P hP k P' (Matrix.mulVecLin V) hP'
    (fun z => hex z)
  refine ⟨fun j => wp (e j), V, P', fun j => hwp (e j), hVw, hP'V, hP', hu, ?_⟩
  intro τ i
  have h3 : V *ᵥ wp ⟨τ, i⟩ = Pi.single (e.symm ⟨τ, i⟩) 1 := by
    simpa using hVw (e.symm ⟨τ, i⟩)
  rw [← h3]
  exact (hD (wp ⟨τ, i⟩) (u τ i)).1 (hwp ⟨τ, i⟩)


set_option maxHeartbeats 1000000 in
theorem exists_holPeriods_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1)) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.Pj.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (F.Di k) (fun j => Formalism.L2.Pj.relab c σ (e j).1) B' P ∧ ∀ b ∈ B', (y b).x = F.u k (P b) ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (P b) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((y b).u τ i) := by
  intro E _ _ _ H Dw l Xo c σ g e F A _ _ yA m B φ y hB hφ hmap b₀ hb₀
  have hpts : IsHolTo B (fun b => (y b).x) := by
    have h1 := GlobalTheory.ThetaValueCont.isHolTo_spMap hB (fun b => ((φ b).toRingHom : A →+* ℂ)) (fun a => hφ a)
    have h2 := GlobalTheory.LocLift.isHolTo_comp_hom h1 yA.x
    exact GlobalTheory.LocLift.isHolTo_congr h2 (fun b hb => (hmap b hb).1)
  obtain ⟨B1, k, P0, hB1, hb1, hB1B, hP0, hu0⟩ :=
    F.24 m B (fun b => (y b).x) hB (fun b _ => (y b).2) hpts b₀ hb₀
  have hadp := fun b (hb : b ∈ B1) =>
    exists_adapted E H Dw l Xo c σ g e F (y b) k (P0 b) (hP0.1 b hb) (hu0 b hb)
  choose! W V P' hW hVW hP'V hP' hux hder using hadp
  have hWd : ∀ b' ∈ B1, ∀ j, DifferentiableAt ℂ (fun b => W b j) b' := by
    intro b' hb' j
    refine GlobalTheory.HolFrameMatrix.differentiableAt_coord F k (yA.u (e j).1 (e j).2)
      (fun b => ((φ b).toRingHom : A →+* ℂ)) hB1 hP0 (fun b => W b j) ?_ hb' ?_
    · intro b hb
      have h1 := hW b hb j
      rw [(hmap b (hB1B hb)).2.1, GlobalTheory.HolFrameMatrix.dualMap_eq] at h1
      exact h1
    · intro t
      exact (hφ t).differentiableAt (hB.mem_nhds (hB1B hb'))
  have hVW1 : ∀ b ∈ B1, V b * Matrix.of (fun i j => W b j i) = 1 := by
    intro b hb
    ext i j
    have h := congrFun (hVW b hb j) i
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [show (∑ x, V b i x * W b j x) = (V b *ᵥ W b j) i from rfl, h, Pi.single_apply, Matrix.one_apply]
  have hVd : ∀ b' ∈ B1, ∀ i j, DifferentiableAt ℂ (fun b => V b i j) b' := by
    intro b' hb' i j
    exact GlobalTheory.HolFrameMatrix.differentiableAt_of_mul_eq_one V (fun b => Matrix.of fun i j => W b j i) b'
      (fun i j => differentiableAt_pi.1 (hWd b' hb' j) i)
      (Filter.eventually_of_mem (hB1.mem_nhds hb') hVW1) i j
  have hPd : ∀ b' ∈ B1, ∀ a, DifferentiableAt ℂ (fun b => P0 b a) b' :=
    fun b' hb' a => (hP0.2 a).differentiableAt (hB1.mem_nhds hb')
  refine ⟨B1, k, P', hB1, hb1, hB1B, ⟨fun b hb => hP' b hb, fun a => ?_⟩, fun b hb => ⟨hux b hb, hder b hb⟩⟩
  intro b' hb'
  have hd : DifferentiableAt ℂ (fun b => V b *ᵥ P0 b a) b' := by
    rw [differentiableAt_pi]
    intro i
    show DifferentiableAt ℂ (fun b => ∑ j, V b i j * P0 b a j) b'
    have hv : ∀ j, DifferentiableAt ℂ (fun b => V b i j) b' := hVd b' hb' i
    have hp : ∀ j, DifferentiableAt ℂ (fun b => P0 b a j) b' := fun j => differentiableAt_pi.1 (hPd b' hb' a) j
    first
      | exact DifferentiableAt.fun_sum fun j _ => (hv j).mul (hp j)
      | fun_prop
      | (convert DifferentiableAt.sum (u := Finset.univ) (fun j _ => (hv j).mul (hp j)) using 1
         ext b
         simp)
  exact hd.differentiableWithinAt.congr (fun b hb => hP'V b hb a) (hP'V b' hb' a)

end GlobalTheory.AdaptedPeriods
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdaptedStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_periods_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => Formalism.L2.Pj.relab c σ (e j).1)) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => Formalism.L2.Pj.toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (F.Di k) (fun j => Formalism.L2.Pj.relab c σ (e j).1) B' P ∧ ∀ b ∈ B', (y b).x = F.u k (P b) ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (P b) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((y b).u τ i) := by
  first | exact @GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted | exact GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted | (intros; apply GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompEmbEqOfFrBor
section -- merged from Development.AbelianVarietyTheory.Proofs.GenericRegularity.EqOfUnitriangularOfEqLowerMul
namespace GlobalTheory.UnitriangularLowerMulEq

open Matrix

theorem eq_of_unitriangular_of_eq_lower_mul {S : Type} [inst : CommRing S] {n : ℕ}
    (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ (i j : Fin n), j < i → A i j = (0 : S)) (hA1 : ∀ (i : Fin n), A i i = (1 : S))
    (hA' : ∀ (i j : Fin n), j < i → A' i j = (0 : S)) (hA'1 : ∀ (i : Fin n), A' i i = (1 : S))
    (hL : ∀ (i j : Fin n), i < j → L i j = (0 : S)) (h : A' = L * A) : A' = A := by
  classical
  have hAb : A.BlockTriangular id := fun i j hji => hA i j hji
  have hA'b : A'.BlockTriangular id := fun i j hji => hA' i j hji
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAb]
    simp [hA1]
  have hu : IsUnit A.det := by rw [hdet]; exact isUnit_one
  have hLeq : L = A' * A⁻¹ := by
    rw [h, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have : Invertible A := A.invertibleOfIsUnitDet hu
  have hLb : L.BlockTriangular id := hLeq ▸ hA'b.mul (Matrix.blockTriangular_inv_of_blockTriangular hAb)
  have hoff : ∀ i j, i ≠ j → L i j = 0 := fun i j hij =>
    (lt_or_gt_of_ne hij).elim (hL i j) fun hji => hLb hji
  have hdiag : ∀ i, L i i = 1 := by
    intro i
    have hii := congrFun (congrFun h i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hki => by rw [hoff i k (Ne.symm hki), zero_mul])
      (by simp), hA1, mul_one, hA'1] at hii
    exact hii.symm
  have hL1 : L = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [hdiag]
    · simp [hoff i j hij, Matrix.one_apply_ne hij]
  rw [h, hL1, Matrix.one_mul]

end GlobalTheory.UnitriangularLowerMulEq
end

open AlgebraicGeometry CategoryTheory Limits NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg.GenericFlagInj

theorem unitri_eq_of_lower {S : Type} [CommRing S] {n : ℕ} (A A' L : Matrix (Fin n) (Fin n) S)
    (hA : ∀ i j, j < i → A i j = 0) (hAd : ∀ i, A i i = 1)
    (hA' : ∀ i j, j < i → A' i j = 0) (hAd' : ∀ i, A' i i = 1)
    (hL : ∀ i j, i < j → L i j = 0) (e : A' = L * A) : A' = A := by
  first
  | exact @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul
  | (apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UnitriangularLowerMulEq.eq_of_unitriangular_of_eq_lower_mul ..)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genPt_inj {Z Z' : Comp Xo c} (h : genPt Z = genPt Z') : Z = Z' := by
  have g : ∀ W : Comp Xo c, IsGenericPoint (genPt W) (W : Set (Xo.XF c)) := fun W =>
    W.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ W.2)
  exact Subtype.ext (by rw [← (g Z).def, ← (g Z').def, h])

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) := by
  symm
  show Spec.map (CommRingCat.ofHom (Spec.preimage (genSp Z ≫ strK)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem genSp_eq {T : Type} [CommRing T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') :
    spMap ψ.toRingHom ≫ genSp Z = spMap ψ'.toRingHom ≫ genSp Z' := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc]
    exact h
  · have e := genSp_strK Z
    have e' := genSp_strK Z'
    rw [Category.assoc, Category.assoc]
    erw [e, e']
    rw [spMap_comp_ring, spMap_comp_ring]
    congr 1
    ext r
    exact (ψ.commutes r).trans (ψ'.commutes r).symm

theorem comp_eq {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] {Z Z' : Comp Xo c} (ψ : kap Z →ₐ[c.F] T)
    (ψ' : kap Z' →ₐ[c.F] T) (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z') : Z = Z' := by
  obtain ⟨p⟩ : Nonempty (Sp T) := inferInstanceAs (Nonempty (PrimeSpectrum T))
  have e := congrArg (fun f : Sp T ⟶ Xo.XF c => f p) (genSp_eq ψ ψ' h)
  simp only [Scheme.Hom.comp_apply, genSp] at e
  apply genPt_inj
  exact (Scheme.fromSpecResidueField_apply _ _).symm.trans (e.trans (Scheme.fromSpecResidueField_apply _ _))

theorem emb_eq {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (ψ ψ' : kap Z →ₐ[c.F] T)
    (h : spMap ψ.toRingHom ≫ xGen Z = spMap ψ'.toRingHom ≫ xGen Z) : ψ = ψ' := by
  have e := genSp_eq ψ ψ' h
  haveI : Mono (genSp Z) := by unfold genSp; infer_instance
  have e2 : spMap ψ.toRingHom = spMap ψ'.toRingHom := (cancel_mono (genSp Z)).1 e
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
  exact AlgHom.coe_ringHom_injective e3

noncomputable def resKap {T : Type} [CommRing T] [Algebra c.F T] {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T) : kap Z →ₐ[c.F] T :=
  { φ.toRingHom.comp (algebraMap (kap Z) (Om Z)) with
    commutes' := fun r => by
      have := φ.commutes r
      rw [gfp_tower] at this
      exact this }

theorem x_eq {T : Type} [CommRing T] [Algebra c.F T] (h : GenFrEx Xo c) {Z : Comp Xo c} (φ : Om Z →ₐ[c.F] T)
    {y : FrPt Xo c T} (hy : FrMap φ (genFr h Z) y) : y.x = spMap (resKap φ).toRingHom ≫ xGen Z := by
  rw [hy.1, (isGenFr_genFr h Z).1, ← Category.assoc, spMap_comp_ring]
  rfl

theorem eq_of_frBor {T : Type} [CommRing T] [Nontrivial T] [Algebra c.F T] (h : GenFrEx Xo c) (Z Z' : Comp Xo c)
    (φ : Om Z →ₐ[c.F] T) (φ' : Om Z' →ₐ[c.F] T) (y y' : FrPt Xo c T) (t : Ix Dw → Tˣ)
    (hy : FrMap φ (genFr h Z) y) (hy' : FrMap φ' (genFr h Z') y') (hb : FrBor t y y') : Z = Z' ∧ HEq φ φ' := by
  have hx := x_eq h φ hy
  have hx' := x_eq h φ' hy'
  have hxx := hx.symm.trans (hb.1.symm.trans hx')
  obtain rfl : Z = Z' := comp_eq _ _ hxx
  refine ⟨rfl, heq_of_eq ?_⟩
  have hψ : resKap φ = resKap φ' := emb_eq _ _ hxx
  obtain ⟨y₀, hy₀, hc⟩ := (isGenFr_genFr h Z).2
  have pull : ∀ (χ : Om Z →ₐ[c.F] T) (w : FrPt Xo c T), FrMap χ (genFr h Z) w → ∀ τ i,
      IsCombAt w.x (fun j => spMap (dualMap (resKap χ).toRingHom) ≫ y₀.u τ j) (fun j => χ (genCoef Z τ i j))
        (w.u τ i) := by
    intro χ w hw τ i
    refine isCombAt_pull χ.toRingHom hw.1 (fun j => ?_) (hw.2.1 τ i) (hc τ i)
    rw [← Category.assoc, spMap_comp_ring, ← dualMap_comp]
    rfl
  have hcoef : ∀ τ i j, φ' (genCoef Z τ i j) = φ (genCoef Z τ i j) := by
    intro τ
    choose cf hd hz hcf using hb.2.1 τ
    have hyx : y.x = spMap (resKap φ).toRingHom ≫ y₀.x := by rw [hx, hy₀]
    have key := unitri_eq_of_lower (Matrix.of fun i j => φ (genCoef Z τ i j))
      (Matrix.of fun i j => φ' (genCoef Z τ i j)) (Matrix.of cf)
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef])
      (fun i j hij => by simp [genCoef, not_lt.2 hij.le, hij.ne'])
      (fun i => by simp [genCoef]) (fun i j hij => hz i j hij) ?_
    · intro i j
      exact congrFun (congrFun key i) j
    · ext i j
      have h1 := pull φ' y' hy' τ i
      rw [← hψ, hb.1] at h1
      have h2 := GlobalTheory.TangentLinear.isCombAt_mulVec E H Dw l Xo T y.x
        (fun j => spMap (dualMap (resKap φ).toRingHom) ≫ y₀.u τ j)
        (fun j => hyx ▸ GlobalTheory.Frames.FramedBaseChange.tan_bc (resKap φ).toRingHom (y₀.tan τ j)) (y.u τ)
        (Matrix.of fun j i => φ (genCoef Z τ i j)) (cf i) (y'.u τ i) (pull φ y hy τ) (hcf i)
      have ht : IsTanAt y.x (y'.u τ i) := hb.1 ▸ y'.tan τ i
      rw [hyx] at h1 h2 ht
      have h3 := (GlobalTheory.Frames.eigenbasis_baseChange E H Dw l Xo c _ T (resKap φ) y₀ τ _ ht (y'.eig τ i)).unique h1 h2
      have h4 := congrFun h3 j
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply] at h4
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h4]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  apply AlgHom.coe_ringHom_injective
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial (FlagVar Dw) (kap Z))) ?_
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
  · exact AlgHom.congr_fun hψ r
  · obtain ⟨τ, ⟨i, j⟩, hij⟩ := v
    have := hcoef τ i j
    simp only [genCoef, dif_pos (show i < j from hij)] at this
    exact this.symm

end GlobalTheory.Reg.GenericFlagInj
end
