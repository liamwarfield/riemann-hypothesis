module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetPointGood
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualHalfLatticeDetectingCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StarBoundOfMultiplicity
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitEmbeddingValuedEqIntValuationInteger
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftDatumThetaSeriesRightInvariantCoreLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlacePairMovesLatticeVacuumReading

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.ConjHalfDual

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

variable {D : D7}

theorem cA_cA_self (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show a ⊗ₜ[D.host.F] D.sp.cm.sig (D.sp.cm.sig x) = a ⊗ₜ[D.host.F] x
    congr 1
    exact star_star x
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

theorem infPart_cA_of_zero {z : AE D} (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  have key : ∀ w : AE D, infPart D (cA D w) =
      Algebra.TensorProduct.map (AlgHom.id D.host.F (Ainf D.host.F)) D.sp.cm.sig (infPart D w) := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), map_add (f := _)]
  rw [key, h, map_zero]

theorem symplO_add_right' (S T : HSp D) (x y y' : WO S T) :
    symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO; rw [hO_add_right, mul_add, map_add (f := _)]

theorem hO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    hO S T x (g • y') = 0 := by
  unfold hO
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ =>
    Finset.sum_eq_zero fun d _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul, ← hx d a, map_mul]
  calc incA D (S.gram⁻¹ a b) * (cA D g * cA D (y' c b)) * incA D (T.gram c d) * (f * x d a)
      = (cA D g * f) * (incA D (S.gram⁻¹ a b) * cA D (y' c b) * incA D (T.gram c d) * x d a) := by ring
    _ = 0 := by rw [hfg, zero_mul]

theorem symplO_eq_zero_of {f g : AE D} (hfg : cA D g * f = 0) {S T : HSp D} {x y' : WO S T} (hx : IsHalf f x) :
    symplO S T x (g • y') = 0 := by
  unfold symplO; rw [hO_eq_zero_of hfg hx, mul_zero, map_zero]

theorem mem_latO_iff_of_conjHalf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  intro D ψ S T ΛS ΛT hψ hS hT e he hec hinf hfin u hu
  have key := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT).1
  have hcc : cA D (cA D e) = e := cA_cA_self e
  have hcidem : cA D e * cA D e = cA D e := by rw [← map_mul, he]
  have hcinf : infPart D (cA D e) = 0 := infPart_cA_of_zero hinf
  constructor
  · intro hmem l hl _
    have hl0 : l.map (infPart D) = 0 := by
      ext i j; exact latAll_infPart hl i j
    exact (key l hl0).1 hl u hmem
  · intro h
    have hu0 : u.map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.zero_apply, ← hu i j, map_mul, hcinf, zero_mul]
    refine (key u hu0).2 fun u' hu' => ?_
    have hdec : u' = e • u' + (cA D e • u' + (1 - e - cA D e) • u') := by
      ext i j; simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
    have m1 : e • u' ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) :=
      smul_mem_latAll hfin hu'
    have hh1 : IsHalf e (e • u') := fun i j => by
      rw [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, he]
    have t1 : ψ (symplO S T u (e • u')) = 1 := by
      rw [GlobalTheory.SplitScalar.symplO_skew, AddChar.map_neg_eq_inv, h _ m1 hh1, inv_one]
    have t2 : symplO S T u (cA D e • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by rw [hcc]; exact hec) hu
    have t3 : symplO S T u ((1 - e - cA D e) • u') = 0 :=
      symplO_eq_zero_of (f := cA D e) (by
        rw [map_sub, map_sub, map_one, hcc]
        linear_combination (-1 : AE D) * hcidem - hec) hu
    rw [hdec, symplO_add_right', symplO_add_right', t2, t3, add_zero, add_zero, t1]

end GlobalTheory.ConjHalfDual

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDualStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ e : AE D, e * e = e → e * cA D e = 0 → infPart D e = 0 → finPart D e ∈ intAE D → ∀ u : WO S T, IsHalf (cA D e) u → (u ∈ latO S T ΛS ΛT (fun _ => True) ↔ ∀ l ∈ latO S T ΛS ΛT (fun _ => True), IsHalf e l → ψ (symplO S T l u) = 1) := by
  first | exact @GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | exact GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf | (intros; apply GlobalTheory.ConjHalfDual.mem_latO_iff_of_conjHalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallField
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FixBaseSmall

theorem host_mem (D : D7) (hgal : IsGalois ℚ D.LL0) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ x ∈ (embLL0 D).fieldRange := by
  let e : D.host.E →+* ↥D.LL0 := D.embE.codRestrict D.LL0 fun y => D.hostField_le_fixedField y
  have hsp := Normal.splits hgal.to_normal (e x)
  have hmin : minpoly ℚ (e x) = minpoly ℚ x := minpoly.algHom_eq e.toRatAlgHom e.injective x
  rw [hmin] at hsp
  have himg := Polynomial.Splits.image_rootSet hsp (embLL0 D).toRatAlgHom
  have hx : φ x ∈ (minpoly ℚ x).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x), ?_⟩
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom x (minpoly ℚ x)
    rw [minpoly.aeval, map_zero] at this
    exact this
  rw [← himg] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact ⟨y, hy⟩

theorem core_mem {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (hLaws : LawsJ T) (ha : AlgTie T) (j : Fin D.R.m) (a : T.Q.c.F) : (a : ℂ) ∈ (embLL0 D).fieldRange := by
  refine ⟨S.kKs ((YS.fi j).eK.symm a), ?_⟩
  have h1 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hLaws.pins.2.2.1
  change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm a) : ↥D.LL0) : D.what₂.LL) = (a : ℂ)
  rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h1 a

theorem three_le_mod (D : D7) : 3 ≤ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have h2 := D.host.pde_prime.two_le
  have h3 := D.host.pde'_prime.two_le
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
  omega

theorem fixesCurve_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : ℂ ≃+* ℂ)
    (N : ℕ) (hN : N ≠ 0) (h : GlobalTheory.CompRat.FixesCurve H τ N) : GlobalTheory.CompRat.FixesCurve H τ 1 := by
  obtain ⟨C, ι, hpb, hact⟩ := h
  refine ⟨C, ι, hpb, fun a => ?_⟩
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have key := hact ((N : ℤ) * a.1, (N : ℤ) * a.2)
  have e1 : GlobalTheory.CompRat.wC H ((N : ℤ) * a.1, (N : ℤ) * a.2) = (N : ℂ) * GlobalTheory.CompRat.wC H a := by
    simp only [GlobalTheory.CompRat.wC]; push_cast; ring
  rw [e1] at key
  have e2 : GlobalTheory.CompRat.wC H (1, 0) * ((N : ℂ) * GlobalTheory.CompRat.wC H a) / (N : ℂ) =
      GlobalTheory.CompRat.wC H (1, 0) * GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  have e3 : (N : ℂ) * GlobalTheory.CompRat.wC H a / (N : ℂ) = GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  rw [e2, e3] at key
  exact key

theorem curve_fix (hRF : GlobalTheory.NT.RayField) (D : D7) (T : CoreJ D) (hLaws : LawsJ T)
    (hRay : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1 := by
  set N := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' with hNdef
  have hN := three_le_mod D
  let Fc : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange
  let σ : Fc →+* ℂ := Fc.val.toRingHom
  have hRay' : RayIn D N σ.fieldRange := by
    obtain ⟨L, i1, i2, i3, i4, h1, jj, h2, h3⟩ := hRay
    refine ⟨L, i1, i2, i3, i4, h1, jj, h2, fun x => ?_⟩
    obtain ⟨y, hy⟩ := h3 x
    exact ⟨⟨jj x, ⟨y, hy⟩⟩, rfl⟩
  have hC := GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hLaws.pins.1 N hN Fc σ hRay'
  have hfix := hC τ fun z hz => by
    obtain ⟨y, hy⟩ := hz
    exact hτ z ⟨y, hy⟩
  exact fixesCurve_one T.Q.H τ N (by omega) hfix

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

theorem split_mem (D : D7) (C : Formalism.L2.Host.CharFrame D) (hV : Formalism.L2.Host.ValLL0 D C) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ∈ (embLL0 D).fieldRange := by
  have hu : (C.mu0 i).UnrAt P := (C.isMu0 i).unr P fun k hk => hP (by
    simp only [Formalism.L2.Host.OverP] at hk
    fin_cases k
    · push_cast; exact Ideal.mul_mem_right _ _ hk
    · push_cast; exact Ideal.mul_mem_left _ _ hk)
  have he : C.eta.UnrAt P := C.isEta.unr P
  obtain ⟨y1, hy1⟩ := hV.mu0 i P hu
  obtain ⟨y2, hy2⟩ := hV.eta P he
  refine ⟨y1 * y2⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hy1, hy2]
  have hN : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot)
  have hNn : (0 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero hNn]; exact hN
  have hc : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((1 / 2 : ℝ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hNn, Real.sqrt_eq_rpow,
      Real.rpow_neg hNn, Complex.ofReal_inv]
  have hval : (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) = (((C.mu0 i).val P : ℂˣ) : ℂ) * (((C.eta).val P : ℂˣ) : ℂ)⁻¹ := by
    show ((((C.mu0 i).val P * (C.eta.val P)⁻¹ : ℂˣ)) : ℂ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hval]
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one, hc]
  have hne : (((C.eta).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hs' : ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

theorem fixBase_of_fixes : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (τ : ℂ ≃+* ℂ), (∀ z ∈ (embLL0 D).fieldRange, τ z = z) → FixBase T Rl.toRealDat j τ := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ hLaws hCore hFW hTie hgal hVal hRay hroots j τ hτ
  refine ⟨fun a => hτ _ (core_mem T Rl cG S YS hLaws hTie.alg j a), fun φ x => hτ _ (host_mem D hgal φ x),
    curve_fix hRF D T hLaws hRay τ hτ, fun P hP => hτ _ (split_mem D Rl.C hVal j P hP),
    fun PP hPP x => hτ _ (GlobalTheory.T.typePlace_residueCharacters_values_mem_smallField D Γ Pl0 I0 T0 A3 T Rl cG S YS F hLaws hCore hgal hVal hroots j PP hPP x)⟩

end GlobalTheory.FixBaseSmall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixesUntwistedTupleDataOfFixesSmallFieldStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixes_untwistedTupleData_of_fixes_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (τ : ℂ ≃+* ℂ), (∀ z ∈ (embLL0 D).fieldRange, τ z = z) → FixBase T Rl.toRealDat j τ := by
  first | exact @GlobalTheory.FixBaseSmall.fixBase_of_fixes | exact GlobalTheory.FixBaseSmall.fixBase_of_fixes | (intros; apply GlobalTheory.FixBaseSmall.fixBase_of_fixes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.IdemResLift


set_option maxHeartbeats 800000 in
theorem exists_int_lift : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  intro D Q es hI hc Y
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hI i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have horth : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj hji =>
    GlobalTheory.PlaceDatum.idemAt_mul (hI i hi) (hI j hj) (hx i hi j hj) (hx j hj i hi) hji
  have hfix : ∀ j ∈ Q, (∑ i ∈ Q, es i) * es j = es j := by
    intro j hj
    rw [Finset.sum_mul, Finset.sum_eq_single j (fun i hi hij => by rw [mul_comm]; exact horth j hj i hi hij)
      (fun h => absurd hj h), h1 j hj]
  choose a ha using fun P : Pl D.host.E => Ideal.Quotient.mk_surjective (Y P)
  have hint : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)).1
  have hmem : ∀ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D)
      ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP => Subring.mul_mem _ (hint P hP) (Subtype.property _)
  let T : ∀ P, P ∈ Q → Formalism.L2.Herm.intAf D.host.F D.host.E := fun P hP =>
    ⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)
  refine ⟨∑ P ∈ Q, toEAf D (es P) * ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D),
    Subring.sum_mem _ hmem, ?_, ?_⟩
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [← mul_assoc, ← RingHom.map_mul (toEAf D), hfix P hP]
  · intro P hP
    have hN : (⟨_, Subring.sum_mem _ hmem⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ∑ x ∈ Q.attach, T x.1 x.2 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact (Finset.sum_attach Q (fun P => toEAf D (es P) *
        ((oToS D.host.F D.host.E (a P) : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D))).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hN, map_sum, Finset.sum_eq_single ⟨P, hP⟩]
    · obtain ⟨h, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hI P hP)
      show resS D.host.F P (⟨toEAf D (es P), hint P hP⟩ * oToS D.host.F D.host.E (a P)) = Y P
      rw [map_mul, resS_oToS, ha, h1, one_mul]
    · rintro ⟨P', hP'⟩ - hne
      have hne' : P' ≠ P := fun h => hne (Subtype.ext h)
      show resS D.host.F P (⟨toEAf D (es P'), hint P' hP'⟩ * oToS D.host.F D.host.E (a P')) = 0
      rw [map_mul, GlobalTheory.TameProd.resS_idem_eq_zero (hI P' hP') hne', zero_mul]
    · intro h; exact absurd (Finset.mem_attach Q _) h

end GlobalTheory.IdemResLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralLiftResiduesIdempotentSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_lift_residues_idempotentSum : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → ∀ Y : ∀ PP : Pl D.host.E, kP PP, ∃ N : EAf D, ∃ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N ∧ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = Y PP := by
  first | exact @GlobalTheory.IdemResLift.exists_int_lift | exact GlobalTheory.IdemResLift.exists_int_lift | (intros; apply GlobalTheory.IdemResLift.exists_int_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBounded
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

open GlobalTheory.RSJ

namespace GlobalTheory.ZEulProps

theorem norm_prod_le (W W' c₁ c₂ c₃ : ℂ) :
    ‖W * conj W' * c₁ * c₂ * c₃‖ ≤ (‖W * conj W * c₁ * c₂ * c₃‖ + ‖W' * conj W' * c₁ * c₂ * c₃‖) / 2 := by
  simp only [norm_mul, Complex.norm_conj]
  have hK : 0 ≤ ‖c₁‖ * ‖c₂‖ * ‖c₃‖ := by positivity
  nlinarith [mul_nonneg (sq_nonneg (‖W‖ - ‖W'‖)) hK]

theorem psiN_mul_conj {E : Type} [Field E] [NumberField E] {a : ℕ} (u : GA E a) :
    GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp [GlobalTheory.JSW.psiN, Circle.norm_coe]

theorem lastRow_unip {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {m : ℕ} {u : GA E (m + 1)}
    (hu : u ∈ GlobalTheory.CellDec.NA E (m + 1)) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := by
  have h := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
  refine GlobalTheory.ZUnf.lastRow_mul_of_row fun l => ?_
  by_cases hl : l = Fin.last m
  · subst hl; rw [h.2, Matrix.one_apply_eq]
  · have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
    rw [h.1 _ _ hlt, Matrix.one_apply_ne (Ne.symm hl)]

theorem detPow_unip {E : Type} [Field E] [NumberField E] {a : ℕ} {u : GA E a} (hu : u ∈ GlobalTheory.CellDec.NA E a) (x : ℝ) :
    GlobalTheory.RSJ.detPow E a x u = 1 := by
  have hd : Matrix.GeneralLinearGroup.det u = 1 := Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu)
  unfold GlobalTheory.RSJ.detPow chiDet
  rw [MonoidHom.comp_apply, hd, map_one]
  simp

end GlobalTheory.ZEulProps

theorem GlobalTheory.ZEulProps.uInt_props : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  intro E _ _ _ m φ φ' Φ N x hW hW' hl hl' hΦ _
  refine ⟨?_, fun u hu g => ?_, fun g => ?_⟩
  · exact GlobalTheory.ZUnfTheta.measurable_integrand hW.measurable hW'.measurable hΦ N x
  · have hu' : u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)) := (GlobalTheory.SmGL.mem_unipB (Ad E)).1 hu
    unfold GlobalTheory.ZEul.uInt
    rw [GlobalTheory.ZEulProps.lastRow_unip hu g, mul_assoc u g, hl u hu', hl' u hu', GlobalTheory.RSJ.Model.detPow_mul,
      GlobalTheory.ZEulProps.detPow_unip hu x, one_mul, map_mul]
    have h1 := GlobalTheory.ZEulProps.psiN_mul_conj u
    linear_combination (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
      conj (GlobalTheory.JSW.whit φ' (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
      Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
      (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ)) * h1
  · unfold GlobalTheory.ZEul.uInt
    exact GlobalTheory.ZEulProps.norm_prod_le _ _ _ _ _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBoundedStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (φ φ' : GA E (m + 1) → ℂ)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ),
    Continuous (GlobalTheory.JSW.whit φ) → Continuous (GlobalTheory.JSW.whit φ') →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g) →
    Continuous Φ → (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    Measurable (GlobalTheory.ZEul.uInt φ φ' Φ N x) ∧
    (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, GlobalTheory.ZEul.uInt φ φ' Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ' Φ N x g) ∧
    ∀ g, ‖GlobalTheory.ZEul.uInt φ φ' Φ N x g‖ ≤ (‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ + ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖) / 2 := by
  first | exact @GlobalTheory.ZEulProps.uInt_props | exact GlobalTheory.ZEulProps.uInt_props | (intros; apply GlobalTheory.ZEulProps.uInt_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReduction
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
namespace GlobalTheory.IdemKerDiv

theorem resS_eq_zero_iff_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (PP : Pl E) (x : Formalism.L2.Herm.intAf F E) :
    resS F PP x = 0 ↔ x ∈ idS F PP.asIdeal := by
  simp [resS, Ideal.Quotient.eq_zero_iff_mem]

theorem intAt_inv_mul {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    {ϖ p : 𝓞 E} (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2) (hp : p ∈ P.asIdeal) :
    Formalism.L2.Col.IntAt P ((ϖ : E)⁻¹ * (p : E)) := by
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hϖ2 (Ideal.zero_mem _)
  obtain ⟨J, hJ⟩ : P.asIdeal ∣ Ideal.span {ϖ} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hϖ)
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hϖ2
    have : Ideal.span {ϖ} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self ϖ)
  obtain ⟨s, hsJ, hsP⟩ := Set.not_subset.mp hJP
  have hsp : s * p ∈ Ideal.span {ϖ} := by
    rw [hJ, mul_comm s p]; exact Ideal.mul_mem_mul hp hsJ
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hsp
  refine ⟨r, s, hsP, ?_⟩
  have hϖE : (ϖ : E) ≠ 0 := by exact_mod_cast hϖ0
  have h1 : (r : E) * (ϖ : E) = (s : E) * (p : E) := by exact_mod_cast hr
  show (s : E) * ((ϖ : E)⁻¹ * (p : E)) = (r : E)
  field_simp
  linear_combination -h1

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem integral_div_iff : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → ∀ N : EAf D, ∀ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N → (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = 0) := by
  intro D Q es ϖ hid horth hϖ N hN hfix
  have hE : ∀ P ∈ Q, toEAf D (es P) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun P hP => (GlobalTheory.IdemRes.resS_idem_eq_one D (es P) P (hid P hP)).1
  have hϖ0 : ∀ P ∈ Q, ((ϖ P : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro P hP h
    have : ϖ P = 0 := by exact_mod_cast h
    exact (hϖ P hP).2 (this ▸ Ideal.zero_mem _)
  have hmul : ∀ P ∈ Q, ∀ P' ∈ Q, es P * es P' = if P = P' then es P else 0 := by
    intro P hP P' hP'
    split_ifs with h
    · subst h; exact (hid P hP).1.1
    · exact GlobalTheory.SplitIdeleModulus.idemAt_mul_eq_zero (hid P hP) (hid P' hP') h
  have hpp : (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))) *
      (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E)⁻¹)) = ∑ P ∈ Q, es P := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro P hP
    rw [Finset.sum_eq_single P]
    · calc es P * incA D (ϖ P : D.host.E) * (es P * incA D ((ϖ P : D.host.E))⁻¹)
            = (es P * es P) * incA D ((ϖ P : D.host.E) * (ϖ P : D.host.E)⁻¹) := by
              rw [map_mul]; ring
          _ = es P := by rw [(hid P hP).1.1, mul_inv_cancel₀ (hϖ0 P hP), map_one, mul_one]
    · intro P' hP' hne
      calc es P * incA D (ϖ P : D.host.E) * (es P' * incA D ((ϖ P' : D.host.E))⁻¹)
            = (es P * es P') * incA D ((ϖ P : D.host.E) * (ϖ P' : D.host.E)⁻¹) := by
              rw [map_mul]; ring
          _ = 0 := by rw [hmul P hP P' hP', if_neg (Ne.symm hne), zero_mul]
    · intro h; exact absurd hP h
  have hoToS : ∀ x : 𝓞 D.host.E,
      ((oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := by
    intro x; rw [GlobalTheory.IdemIntegral.toEAf_incA]; rfl
  constructor
  · intro hM PP hPP
    refine (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) PP ⟨N, hN⟩).mpr ?_
    obtain ⟨M, hMdef⟩ : ∃ M, M = toEAf D (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))⁻¹) * N :=
      ⟨_, rfl⟩
    rw [← hMdef] at hM
    let eI : Pl D.host.E → Formalism.L2.Herm.intAf D.host.F D.host.E :=
      fun P => if h : P ∈ Q then ⟨toEAf D (es P), hE P h⟩ else 0
    have hsplit : (⟨N, hN⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
        (∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P)) * ⟨M, hM⟩ := by
      apply Subtype.ext
      have hs : ((∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          toEAf D (∑ P ∈ Q, es P * incA D ((ϖ P : D.host.E))) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        push_cast
        apply Finset.sum_congr rfl
        intro P hP
        simp only [eI, dif_pos hP, map_mul, hoToS]
      show N = ((∑ P ∈ Q, eI P * oToS D.host.F D.host.E (ϖ P) :
          Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) * M
      rw [hs, hMdef, ← mul_assoc, ← map_mul, hpp, hfix]
    rw [hsplit]
    refine Ideal.mul_mem_right _ _ (Ideal.sum_mem _ fun P hP => ?_)
    by_cases hPe : P = PP
    · subst hPe
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hϖ P hP).1)
    · refine Ideal.mul_mem_right _ _ ?_
      refine (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) PP _).mp ?_
      simp only [eI, dif_pos hP]
      exact GlobalTheory.TameProd.resS_idem_eq_zero (hid P hP) hPe _
  · intro hres
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul]
    refine Subring.sum_mem _ fun P hP => ?_
    have hmem : (⟨N, hN⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈
        Ideal.map (oToS D.host.F D.host.E) P.asIdeal :=
      (resS_eq_zero_iff_mem (F := D.host.F) (E := D.host.E) P ⟨N, hN⟩).mp (hres P hP)
    have key : ∀ x : Formalism.L2.Herm.intAf D.host.F D.host.E,
        x ∈ Ideal.map (oToS D.host.F D.host.E) P.asIdeal →
        toEAf D (es P * incA D ((ϖ P : D.host.E))⁻¹) * (x : EAf D) ∈
          Formalism.L2.Herm.intAf D.host.F D.host.E := by
      intro x hx
      change x ∈ Submodule.span _ _ at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, hp, rfl⟩ := hy
        rw [hoToS, ← map_mul, mul_assoc, ← map_mul]
        exact GlobalTheory.IdemIntegral.mem_of_idemAt (hid P hP) (intAt_inv_mul P (hϖ P hP).1 (hϖ P hP).2 hp)
      | zero => simp
      | add a b _ _ ha hb =>
        rw [Subring.coe_add, mul_add]; exact add_mem ha hb
      | smul a b _ hb =>
        rw [smul_eq_mul, Subring.coe_mul, mul_left_comm]; exact mul_mem a.2 hb
    exact key _ hmem

end GlobalTheory.IdemKerDiv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumIntegralDivUniformisersIffReductionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero : ∀ (D : D7) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → ∀ N : EAf D, ∀ hN : N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, toEAf D (∑ PP ∈ Q, es PP) * N = N → (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ PP ∈ Q, resS D.host.F PP ⟨N, hN⟩ = 0) := by
  first | exact @GlobalTheory.IdemKerDiv.integral_div_iff | exact GlobalTheory.IdemKerDiv.integral_div_iff | (intros; apply GlobalTheory.IdemKerDiv.integral_div_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOff
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellDec.TlComm

theorem tl_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  intro E _ _ n S ϖ l p hp
  have key : ∀ {R : Type} [CommRing R] (c : Ad E →+* R),
      (Matrix.GeneralLinearGroup.map c p = 1 ∨ Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1) = 1) →
      Matrix.GeneralLinearGroup.map c (p * GlobalTheory.CellDec.tl n ϖ l.1) =
        Matrix.GeneralLinearGroup.map c (GlobalTheory.CellDec.tl n ϖ l.1 * p) := by
    intro R _ c h
    rw [map_mul, map_mul]
    rcases h with h | h <;> rw [h] <;> simp
  refine GlobalTheory.JSW.GA_ext (key _ (Or.inr ?_)) fun v => key _ ?_
  · exact map_cornerGL_of_zero _ _ (fun x => rfl) _
  · by_cases hv : v ∈ S
    · refine Or.inr ?_
      rw [GlobalTheory.CellDec.tl, finGL, map_cornerGL_of_hom (sFin E) ((pLoc E v).comp (pFin E)) (pLoc E v) (fun x => rfl)]
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [Matrix.GeneralLinearGroup.map_apply, GlobalTheory.SmGL.val_diagT]
      have hl : l.1 v = 0 := l.2 v hv
      by_cases hij : i = j
      · subst hij
        rw [Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq]
        show ((ϖ v ^ ((Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l.1) v) : (v.adicCompletion E)ˣ) :
          v.adicCompletion E) = 1
        rw [Finsupp.mapRange_apply, hl, Pi.zero_apply, zpow_zero, Units.val_one]
      · simp [Matrix.diagonal_apply, hij, Matrix.one_apply]
    · exact Or.inl (hp v hv)

end GlobalTheory.CellDec.TlComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerCommuteOfOneOffStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_commute_of_one_off : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : GlobalTheory.CellDec.abelian₂ E n S) (p : GA E n),
    (∀ w ∉ S, Matrix.GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) p = 1) →
    p * GlobalTheory.CellDec.tl n ϖ l.1 = GlobalTheory.CellDec.tl n ϖ l.1 * p := by
  first | exact @GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | exact GlobalTheory.CellDec.TlComm.tl_commute_of_one_off | (intros; apply GlobalTheory.CellDec.TlComm.tl_commute_of_one_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrix
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.AdjHalfLift

open GlobalTheory.AdelicLatMove

theorem gramInv_mul_gram {D : D7} (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit S),
    Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem cF_cF {D : D7} (w : EAf D) : cF D (cF D w) = w := by
  obtain ⟨Z, -, rfl⟩ := GlobalTheory.HalfDuality.exists_lift (D := D) w
  exact GlobalTheory.PlaceVec.cF_cF_toEAf Z


set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_half_frMapAdj : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  intro D S T βS βT e hee z hz
  choose L hL0 hL using fun t : EAf D => GlobalTheory.HalfDuality.exists_lift (D := D) t
  let N : Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
    HMul.hMul (HMul.hMul (HMul.hMul (S.gram.map (eToEAf D)) βS.val) z) (HMul.hMul (βT⁻¹).val ((T.gram⁻¹).map (eToEAf D)))
  let X : Matrix (Fin T.rank) (Fin S.rank) (EAf D) := Matrix.of fun i j => cF D (N j i)
  refine ⟨Matrix.of fun i j => cA D e * L (X i j), fun i j => ?_, fun i j => ?_, ?_⟩
  · simp only [Matrix.of_apply, ← mul_assoc, ← map_mul, hee]
  · simp only [Matrix.of_apply, map_mul, hL0, mul_zero]
  · have hcc : cF D (toEAf D (cA D e)) = toEAf D e := by
      rw [← toEAf_cA, GlobalTheory.DualPairCheck.cA_cA]
    have hY : (((Matrix.of fun i j => cA D e * L (X i j) : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D e • N := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, map_mul, hL, X, cF_cF, hcc,
        Matrix.smul_apply, smul_eq_mul]
    rw [GlobalTheory.PlaceVec.frMapAdj_eq, hY, Matrix.mul_smul, Matrix.smul_mul]
    have e1 : HMul.hMul (HMul.hMul (HMul.hMul (βS⁻¹).val ((S.gram⁻¹).map (eToEAf D))) N)
        (HMul.hMul (T.gram.map (eToEAf D)) βT.val) = z :=
      GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ z (gramInv_mul_gram S) (Units.inv_mul βS)
        (gramInv_mul_gram T) (Units.inv_mul βT)
    rw [e1]
    exact Matrix.ext fun i j => hz i j

end GlobalTheory.AdjHalfLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateHalfPrescribedAdjointFrameMatrixStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e : AE D), e * e = e → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (EAf D), (∀ i j, toEAf D e * z i j = z i j) → ∃ y : WO S T, IsHalf (cA D e) y ∧ (∀ i j, infPart D (y i j) = 0) ∧ frMapAdj S T βS βT y = z := by
  first | exact @GlobalTheory.AdjHalfLift.exists_half_frMapAdj | exact GlobalTheory.AdjHalfLift.exists_half_frMapAdj | (intros; apply GlobalTheory.AdjHalfLift.exists_half_frMapAdj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonal
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

open Matrix

namespace GlobalTheory.CellDecNat

theorem glExt {E : Type} [Field E] [NumberField E] {n : ℕ} {x y : GL (Fin n) (Af E)}
    (h : ∀ w, GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y) : x = y :=
  Units.ext (Matrix.ext fun i k => IsDedekindDomain.FiniteAdeleRing.ext _ fun v =>
    congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i k) (h v))

theorem tl_eq_jsw_tl (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ))
    (h : ∀ w i, ((l' w i : ℕ) : ℤ) = l w i) : GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  classical
  unfold GlobalTheory.CellDec.tl GlobalTheory.JSW.tl
  have hm : (List.map (fun w => finGL E n (locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w)))) l'.support.toList).prod =
      finGL E n (List.map (fun w => locGL E n w (GlobalTheory.JSW.diagPow (ϖ w) (l' w))) l'.support.toList).prod := by
    rw [map_list_prod, List.map_map]; rfl
  rw [hm]
  congr 1
  apply glExt
  intro w
  rw [map_list_prod, List.map_map,
    List.prod_map_eq_pow_single w _ (fun v hv _ => by simp only [Function.comp_apply]; exact pLoc_locGL_of_ne (Ne.symm hv) _)]
  simp only [Function.comp_apply, pLoc_locGL]
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hL : ∀ i, (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w = ((l' w i : ℕ) : ℤ) := fun i => by
    rw [Finsupp.mapRange_apply, h]
  change pLoc E w (((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : GL (Fin n) (Af E)) : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases hw : w ∈ l'.support
  · rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (Finset.mem_toList.2 hw), pow_one]
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, zpow_natCast]
      simp [GlobalTheory.JSW.diagPow]
    · simp [Matrix.diagonal_apply_ne _ hij, GlobalTheory.JSW.diagPow]
  · rw [List.count_eq_zero_of_not_mem (by simpa using hw), pow_zero]
    have h0 : l' w = 0 := by simpa using hw
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      change ((ϖ w ^ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l) w : (w.adicCompletion E)ˣ) : w.adicCompletion E) = _
      rw [hL, h0]
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
end GlobalTheory.CellDecNat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicDiagonalUniformizerEqProdLocalDiagonalStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicDiagonalUniformizer_eq_prod_localDiagonal : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ)
    (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) (l' : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℕ)),
    (∀ w i, ((l' w i : ℕ) : ℤ) = l w i) → GlobalTheory.CellDec.tl n ϖ l = GlobalTheory.JSW.tl ϖ l' := by
  first | exact @GlobalTheory.CellDecNat.tl_eq_jsw_tl | exact GlobalTheory.CellDecNat.tl_eq_jsw_tl | (intros; apply GlobalTheory.CellDecNat.tl_eq_jsw_tl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslates
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.VacTransFix

theorem nsmul_cancel {D : D7} {V W : HSp D} {M : ℕ} (hM : M ≠ 0) {x x' : WO V W} (h : M • x = M • x') : x = x' := by
  set a : AE D := algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) ((M : D.host.F)⁻¹)) with ha_def
  have ha : a * (M : AE D) = 1 := by
    have e : (M : AE D) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) (M : D.host.F)) := by
      simp [map_natCast]
    rw [e, ha_def, ← map_mul, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hM), map_one, map_one]
  have key : ∀ z : WO V W, a • (M • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ha, one_smul]
  rw [← key x, h, key]

theorem fix_trans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  obtain ⟨hpair, -, -, -, hsdV, hsdW, -, hcart, hvac⟩ := hP
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.VacFixOpen.exists_open_fix_vacO D ψ θ V W χV χW om hpair.weil hpair.sigV hpair.sigW
    (fun _ => 1) sW (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hpair.std τ) hcart ΛV ΛW hsdV hsdW f₀ hvac
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.LatFixMod.exists_open_keep_cong D V W ΛV ΛW hsdV hsdW (2 * M * M)
    (Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hM)) (Nat.pos_of_ne_zero hM))
  refine ⟨J₁ ⊓ J₂, by rw [Subgroup.coe_inf]; exact hJ₁o.inter hJ₂o, fun k hk hkJ y hy => ?_⟩
  have hθ : IsThetaFunO ψ V W f₀ := hvac.2.theta
  rw [hpair.weil.om_heis k 1 y f₀ hθ, hJ₁ k hk hkJ.1]
  obtain ⟨l, hl, e⟩ := (hJ₂ k hk hkJ.2).2 (M • y) hy
  have hlin : actO V W k 1 (M • y) = M • actO V W k 1 y :=
    (AddMonoidHom.mk' (actO V W k 1) (GlobalTheory.LatNhds.actO_add k 1)).map_nsmul M y
  have e2 : M • actO V W k 1 y = M • (y + 2 • (M • l)) := by
    rw [← hlin, e, smul_add, smul_smul, smul_smul, show 2 * M * M = M * 2 * M by ring]
  rw [nsmul_cancel hM e2]
  refine GlobalTheory.AdForm.SplitGen.heisO_add_two ψ (hvac.2.lat.1 _ (AddSubgroup.nsmul_mem _ hl M)) ?_
  rw [GlobalTheory.RatSelfDual.symplO_nsmul]
  exact GlobalTheory.LatVac.char_sympl_eq_one hvac.1 hsdV hsdW hy hl

end GlobalTheory.VacTransFix

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOpenSubgroupFixVacuumTranslatesStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ M : ℕ, M ≠ 0 → ∃ J : Subgroup (Bridge.Gf V), IsOpen (J : Set (Bridge.Gf V)) ∧ ∀ k ∈ GfC V, fin V k ∈ J → ∀ y : WO V W, M • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → om (k, 1) (heisO ψ V W y f₀) = heisO ψ V W y f₀ := by
  first | exact @GlobalTheory.VacTransFix.fix_trans | exact GlobalTheory.VacTransFix.fix_trans | (intros; apply GlobalTheory.VacTransFix.fix_trans <;> assumption)
end
end
