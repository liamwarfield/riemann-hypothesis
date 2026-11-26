module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit

theorem exists_suppAt_grpCo_eq : ∀ (D : D7) (V : HSp D) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D),
    IsIdemOf φ e → ∀ (B g : GL (Fin V.rank) (Fv D.host.F v)), ∃ h : GA D V, Formalism.L2.Theta.SuppAt e V h ∧ grpCo φ V B h = g := by
  intro D V v φ e he B g
  obtain ⟨h, hs, hr⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) he.1
    (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1 V B g
  refine ⟨h, hs, ?_⟩
  rw [← hr]
  apply Units.ext
  rw [GlobalTheory.SplitHecke.rho_val]
  rfl

end GlobalTheory.DownLift.GenSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedAtSplitPlaceUnitaryMatrixEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportedAtSplitPlace_unitary_matrix_eq : ∀ (D : D7) (V : HSp D) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (B g : GL (Fin V.rank) (Fv D.host.F v)), ∃ h : GA D V, Formalism.L2.Theta.SuppAt e V h ∧ grpCo φ V B h = g := by
  first | exact @GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq | exact GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq | (intros; apply GlobalTheory.DownLift.GenSplit.exists_suppAt_grpCo_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LangExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (WD.lpSum (h := h)) :=
    ⟨fun a b c => by rw [← WD.lpSum_assoc, WD.lpSum_comm a b, WD.lpSum_assoc]⟩
  exact hp.foldr_eq _

theorem charZero_adicCompletion : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

end GlobalTheory.LocLanglands.LangExt


open GlobalTheory.LocLanglands.LangExt in
theorem GlobalTheory.LocLanglands.exists_isLExt : LanglandsExhaustionGL → LanglandsMultisegments → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (r : IrrGL (k := w.adicCompletion E) → WD h), (∃ rc, IsLExt r rc) ∧ ∀ rc, IsLExt r rc → ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp → rc x = r x := by
  intro hX hM E Ω _ _ _ _ _ A w h r
  haveI : CharZero (w.adicCompletion E) := LangExt.charZero_adicCompletion
  refine ⟨⟨fun x => segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList, ?_⟩, ?_⟩
  · intro l x hl
    have hm := Classical.choose_spec (hX (w.adicCompletion E) x)
    have he := (hM (w.adicCompletion E)).1 _ _ x hm hl
    show segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList = segSum r l
    unfold segSum
    apply LangExt.sumList_perm
    apply List.Perm.map
    apply Multiset.coe_eq_coe.1
    rw [Multiset.coe_toList]
    exact he
  · intro rc hrc x hx
    have h1 := hrc [.single x hx] x (single_spec hx).2.2.2
    rw [h1]
    change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) 1)).lpSum (WD.lpZero (h := h)) = r x
    rw [WD.lpSum_zero]
    have h2 := (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r x)).1
    have h3 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
    rw [h3]
    exact h2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinitesimalCharacterInduced
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.BCWords GlobalTheory.SpehInfChar GlobalTheory.BlockCap GlobalTheory.Published

namespace GlobalTheory.NormIndCap

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem tensorSp_update {c : ℕ} {n : Fin c → ℕ} (V : ∀ i, Submodule ℂ (Sm E (n i))) (i : Fin c)
    (m : ∀ j, GA E (n j)) {F : (∀ j, GA E (n j)) → ℂ} (hF : F ∈ tensorSp V) :
    ∃ θ ∈ V i, ∀ y, F (Function.update m i y) = θ.1 y := by
  classical
  let L : ((∀ j, GA E (n j)) → ℂ) →ₗ[ℂ] (GA E (n i) → ℂ) :=
    { toFun := fun F y => F (Function.update m i y), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hle : tensorSp V ≤ ((V i).map (Sm E (n i)).subtype).comap L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨φ, rfl⟩
    refine ⟨(∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) • (φ i).1, (V i).smul_mem _ (φ i).2, ?_⟩
    funext y
    change (∏ j ∈ Finset.univ.erase i, (φ j).1.1 (m j)) * (φ i).1.1 y =
      ∏ j, (φ j).1.1 (Function.update m i y j)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self, mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j hj => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  obtain ⟨θ, hθ, e⟩ := hle hF
  exact ⟨θ, hθ, fun y => (congrFun e y).symm⟩

theorem qdet_block_levi {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (V : ∀ i, Submodule ℂ (Sm E (n i)))
    (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ) (hM : HasInfCharGL (V i) τ M) (u : ℂ) (ψ : Sm E N)
    (hψ : (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorSp V) (m : ∀ j, GA E (n j)) :
    (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) := by
  obtain ⟨θ, hθ, hθe⟩ := tensorSp_update V i m hψ
  have hR : restrLin (stdBlocks n h) m i ψ = θ := Subtype.ext (funext fun y => hθe y)
  have key := LinearMap.congr_fun (qdet_intertwine (restrLin (stdBlocks n h) m i) _ (Eop τ)
    (restrLin_Eop (stdBlocks n h) m i τ) (u + ((n i : ℂ) - 1) / 2)) ψ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hR] at key
  have k2 := congrArg (fun φ : Sm E (n i) => φ.1 (m i)) key
  have hc : Formalism.REAL.qdet (Eop τ) (u + ((n i : ℂ) - 1) / 2) θ = (M.map (u + ·)).prod • θ := hM.2 u θ hθ
  have hm : Function.update m i (m i) = m := Function.update_eq_self i m
  simp only [hc] at k2
  have k3 : (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) (Function.update m i (m i))) =
      (M.map (u + ·)).prod * θ.1 (m i) := k2
  rw [hm, ← hθe, hm] at k3
  exact k3

theorem hasInfCharGL_map_mulChi {a : ℕ} {V : Submodule ℂ (Sm E a)} {τ : E →+* ℂ} {m : Multiset ℂ}
    (h : HasInfCharGL V τ m) (χ : HChar E) :
    HasInfCharGL (V.map (mulChi a χ).toLinearMap) τ (m.map (· + expo χ τ)) := by
  refine ⟨by rw [Multiset.card_map]; exact h.1, ?_⟩
  rintro u _ ⟨φ, hφ, rfl⟩
  change cap τ u (mulChi a χ φ) = _ • mulChi a χ φ
  rw [cap_mulChi, h.2 _ φ hφ, map_smul, Multiset.map_map]
  congr 2
  exact Multiset.map_congr rfl fun x _ => by simp only [Function.comp_apply]; ring

end GlobalTheory.NormIndCap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.SplitIntLift

theorem exists_lift {R K O : Type} [CommRing R] [CommRing K] [CommRing O] {n : ℕ} (S : Subring R) (π : R →+* K)
    (ι : O →+* K) (p : S) (hinj : ∀ x, π x = 0 → (p : R) * x = 0) (hl : ∀ o, ∃ s : S, π s = ι o)
    (h : GL (Fin n) O) (β g : GL (Fin n) R)
    (hg : (Matrix.GeneralLinearGroup.map π β)⁻¹ * Matrix.GeneralLinearGroup.map π g * Matrix.GeneralLinearGroup.map π β =
      Matrix.GeneralLinearGroup.map ι h) :
    ∃ (Y : Matrix (Fin n) (Fin n) S) (u : S), (∀ i j, π (Y i j) = ι (h.1 i j)) ∧ u * Y.det = p ∧
      (p : R) • g.1 = (p : R) • (β.1 * Y.map S.subtype * (β⁻¹).1) := by
  choose Y hY using fun i j => hl (h.1 i j)
  obtain ⟨u, hu⟩ := hl (h⁻¹).1.det
  have eY : (Matrix.of Y).map (π.comp S.subtype) = h.1.map ι := Matrix.ext hY
  refine ⟨Matrix.of Y, p * u, hY, Subtype.ext ?_, ?_⟩
  · have e1 : π ((Matrix.of Y).det : S) = ι h.1.det := by
      rw [RingHom.map_det ι, RingHom.mapMatrix_apply, ← eY, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
      rfl
    have := hinj (u * ((Matrix.of Y).det : S) - 1) (by
      rw [map_sub, map_mul, hu, e1, ← map_mul, ← Matrix.det_mul, Units.inv_mul, Matrix.det_one, map_one, map_one, sub_self])
    push_cast
    linear_combination this
  · have e2 : Matrix.GeneralLinearGroup.map π g = Matrix.GeneralLinearGroup.map π β * Matrix.GeneralLinearGroup.map ι h *
        Matrix.GeneralLinearGroup.map π β⁻¹ := by
      rw [← hg, map_inv]; group
    have e3 : g.1.map π = (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1).map π := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map]
      exact (congrArg Units.val e2).trans (congrArg (fun z => β.1.map π * z * (β⁻¹).1.map π) eY.symm)
    ext i j
    have := hinj (g.1 i j - (β.1 * (Matrix.of Y).map S.subtype * (β⁻¹).1) i j) (by
      rw [map_sub, sub_eq_zero]; exact congrFun (congrFun e3 i) j)
    rw [mul_sub, sub_eq_zero] at this
    exact this

open GlobalTheory.LevSplit GlobalTheory.ParahoricLift Formalism.L2.NTheta GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting

variable {D : D7}

theorem rdE_finSw {v : FinPl D} (φ : SplitProj D v) (a : Formalism.L2.Theta.AE D) : rdE φ (finSw D a) = rdA φ a :=
  GlobalTheory.SplitProjChart.rdE_toEAf φ a

theorem finSw_surjective (z : Formalism.IndefR.Lev.EAf D) : ∃ w, finSw D w = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | tmul x a => exact ⟨(show AF D.host.F from (0, a)) ⊗ₜ x, rfl⟩
  | add a b ha hb =>
    obtain ⟨s, rfl⟩ := ha
    obtain ⟨t, rfl⟩ := hb
    exact ⟨s + t, RingHom.map_add _ _ _⟩

theorem cut_inj {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e)
    (x : Formalism.IndefR.Lev.EAf D) (hx : rdE φ x = 0) : finSw D e * x = 0 := by
  obtain ⟨w, rfl⟩ := finSw_surjective x
  rw [rdE_finSw] at hx
  rw [← RingHom.map_mul, ((GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1.2.1 w).1 hx, RingHom.map_zero]

theorem int_lift {v : FinPl D} {φ : SplitProj D v} {e : Formalism.L2.Theta.AE D} (he : IsIdemOf φ e) (o : OI v) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, rdE φ s = algebraMap (OI v) (Fv D.host.F v) o := by
  obtain ⟨h1, -, -, h4⟩ := (GlobalTheory.SplitProjChart.chart_rdA D v φ e he).1
  obtain ⟨a, ha⟩ := h1 (algebraMap (OI v) (Fv D.host.F v) o)
  refine ⟨⟨finSw D (e * a), swapAE_int ((h4 a).2 ⟨o, ha.symm⟩)⟩, ?_⟩
  show rdE φ (finSw D (e * a)) = _
  rw [rdE_finSw, RingHom.map_mul, he.2.2, one_mul, ha]


set_option maxHeartbeats 1000000 in
theorem lift_of_integral : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  intro D V β Λ N hB P v φ e hP0 he0 red hred h κ hs hκ0
  have he : IsIdemAt e P := (((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ P hP0).2.2 e he0).1
  obtain ⟨p, hp, hpp, hres⟩ := exists_idem_int he
  have hg : (Matrix.GeneralLinearGroup.map (rdE φ) β)⁻¹ * Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) *
      Matrix.GeneralLinearGroup.map (rdE φ) β = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h := by
    rw [← hκ0]
    have : Matrix.GeneralLinearGroup.map (rdE φ) (finE V κ) =
        Matrix.GeneralLinearGroup.map (rdA φ) (Formalism.L2.Theta.matHom V κ) :=
      Units.ext (Matrix.ext fun i j => rdE_finSw φ (Formalism.L2.Theta.mt V κ i j))
    rw [this]
    rfl
  obtain ⟨Y, u, hY, hu', hκ⟩ := exists_lift (Formalism.L2.Herm.intAf D.host.F D.host.E) (rdE φ)
    (algebraMap (OI v) (Fv D.host.F v)) p (fun x hx => hp ▸ cut_inj he0 x hx) (int_lift he0) h β (finE V κ) hg
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hsf := supp_fin V (f := e + cA D e) hs
  have hf : finSw D (e + cA D e) = p + Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) p := by
    rw [RingHom.map_add (f := _), finSw_cA, hp]
  have hSt : finE V κ ∈ St β :=
    mem_St_of_part D.sp.cm.sig V.gram Λ β hB.1 (hatL_selfDual hB) p u hpp (sigR_int p.2) Y hu' (finE V κ)
      (finE_mem_UA V κ) _ hf hsf hκ
  refine ⟨(T3 P e _ hP).2.2.1 κ hs, hSt, Units.ext ?_, fun P' h1 h2 => ?_⟩
  · rw [redFn_of_smul_eq β P _ hSt p hres Y hκ]
    refine Matrix.ext fun i j => ?_
    obtain ⟨hi, hr⟩ := hred (Y i j) (Y i j).2
    exact hr.symm.trans (congrArg red (Subtype.ext (hY i j)))
  · obtain ⟨y, y', hy, hyy, a1, a2⟩ := exists_sep h1 fun h => h2 (isConjPl_symm h)
    obtain ⟨w, hw⟩ := idem_div_int hP y y' hyy a1 a2
    refine redFn_eq_one β P' _ hSt (w * oToS D.host.F D.host.E y) ?_ ?_
    · rw [RingHom.map_mul, resS_oToS, Ideal.Quotient.eq_zero_iff_mem.2 hy, mul_zero]
    · have e1 : ((w * oToS D.host.F D.host.E y : Formalism.L2.Herm.intAf D.host.F D.host.E) : Formalism.IndefR.Lev.EAf D) =
          finSw D (e + cA D e) := hw
      rw [e1]
      exact hsf

end GlobalTheory.DownLift.SplitIntLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceUnitaryIntegralMatrixKeepsLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceUnitary_integralMatrix_keeps_lattice : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∀ (PP : Pl D.host.E) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), (∀ (a : Formalism.IndefR.Lev.EAf D) (ha : a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E), ∃ h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a ∈ v.adicCompletionIntegers D.host.F, red ⟨GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ a, h⟩ = resS D.host.F PP ⟨a, ha⟩) → ∀ (h : GL (Fin V.rank) (OI v)) (κ : GA D V), Formalism.L2.Theta.SuppAt e V κ → grpCo φ V (frCo φ β) κ = Matrix.GeneralLinearGroup.map (algebraMap (OI v) (Fv D.host.F v)) h → κ ∈ GfC V ∧ finE V κ ∈ Formalism.L2.DIV.St β ∧ redFn β PP (finE V κ) = Matrix.GeneralLinearGroup.map red h ∧ ∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn β PP' (finE V κ) = 1 := by
  first | exact @GlobalTheory.DownLift.SplitIntLift.lift_of_integral | exact GlobalTheory.DownLift.SplitIntLift.lift_of_integral | (intros; apply GlobalTheory.DownLift.SplitIntLift.lift_of_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.DownLift.ReadAdj

open GlobalTheory.AdelicLatMove

variable {D : D7}

theorem toEAf_onto : Function.Surjective (toEAf D) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, RingHom.map_zero _⟩
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, RingHom.map_add _ _ _⟩
  | tmul x a => exact ⟨pairA D.host.F 0 a ⊗ₜ[D.host.F] x, rfl⟩

theorem cF_cF (z : Formalism.IndefR.Datum.EAf D) : cF D (cF D z) = z := by
  obtain ⟨a, rfl⟩ := toEAf_onto z
  exact GlobalTheory.PlaceVec.cF_cF_toEAf a

theorem frMapAdj_smul_eq (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (a : AE D)
    (x : WO S T) : frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x := by
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.frMapAdj_eq]
  have : (((a • x : WO S T).map (toEAf D)).map (cF D))ᵀ = toEAf D (cA D a) • ((x.map (toEAf D)).map (cF D))ᵀ :=
    Matrix.ext fun i j => by simp [Matrix.smul_apply, map_mul, toEAf_cA]
  rw [this, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_half (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {e : AE D}
    {x : WO S T} (hx : IsHalf (cA D e) x) : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
  conv_rhs => rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx]
  rw [frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA]

theorem frMapAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x - y) = frMapAdj S T βS βT x - frMapAdj S T βS βT y := by
  have h := GlobalTheory.PlaceVec.frMapAdj_add S T βS βT (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frMapAdj_eq_zero (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Datum.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Datum.EAf D)) {x : WO S T}
    (h : frMapAdj S T βS βT x = 0) : x.map (toEAf D) = 0 := by
  have h1 := congrArg (fun N => (S.gram.map (eToEAf D) * βS.val) * N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D))) h
  simp only [Matrix.mul_zero, Matrix.zero_mul] at h1
  rw [GlobalTheory.PlaceVec.frMapAdj_eq, GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ βS.mul_inv
    (GlobalTheory.PlaceVec.gram_map_mul_inv S) βT.mul_inv (GlobalTheory.PlaceVec.gram_map_mul_inv T)] at h1
  ext i j
  have h2 := congrFun (congrFun h1 j) i
  simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.zero_apply] at h2
  have h3 := congrArg (cF D) h2
  rw [cF_cF, map_zero] at h3
  simpa using h3

theorem phi_toEAf_idem {e : AE D} (he : e * e = e) {F : Type} [CommRing F] (φ : Formalism.IndefR.Datum.EAf D →+* F)
    (hker : ∀ z, φ z = 0 ↔ toEAf D e * z = 0) : φ (toEAf D e) = 1 := by
  have h : toEAf D e * (toEAf D e - 1) = 0 := by
    rw [mul_sub, mul_one, ← map_mul, he, sub_self]
  have := (hker _).2 h
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

theorem finPart_eq_zero_of_toEAf {a : AE D} (h : toEAf D a = 0) : finPart D a = 0 :=
  (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).injective (by rw [map_zero]; exact h)

theorem gram_inv_map_mul (S : HSp D) : (S.gram⁻¹).map (eToEAf D) * S.gram.map (eToEAf D) = 1 :=
  mul_eq_one_comm.1 (GlobalTheory.PlaceVec.gram_map_mul_inv S)

theorem rdAdj_read : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D))
    (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F))
    (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)),
    Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι →
    (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧
    (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧
    (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔
      ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v),
        rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧
    ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) →
      rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) →
      (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  intro D S T βS βT e PP v φ ι hI hL
  obtain ⟨hsurj, hker, hint, hred⟩ := hL
  have hs : IsSplitIdem D e := hI.1
  have hc : IsSplitIdem D (cA D e) := GlobalTheory.SplitScalar.isSplitIdem_conj hs
  have h1 : φ (toEAf D e) = 1 := phi_toEAf_idem hs.1 φ hker
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    choose N hN using fun i j => hsurj (m i j)
    set Q : Matrix (Fin S.rank) (Fin T.rank) (Formalism.IndefR.Datum.EAf D) :=
      (S.gram.map (eToEAf D) * βS.val) * Matrix.of N * ((βT⁻¹).val * (T.gram⁻¹).map (eToEAf D)) with hQ
    choose w hw using fun (i : Fin T.rank) (j : Fin S.rank) => toEAf_onto (Q j i)
    set x' : WO S T := Matrix.of fun i j => cA D (w i j) with hx'
    have hfx : frMapAdj S T βS βT x' = Matrix.of N := by
      rw [GlobalTheory.PlaceVec.frMapAdj_eq]
      have hX : ((x'.map (toEAf D)).map (cF D))ᵀ = Q := by
        ext i j
        simp only [Matrix.transpose_apply, Matrix.map_apply, hx', Matrix.of_apply, toEAf_cA, cF_cF, hw]
      rw [hX, hQ]
      exact GlobalTheory.PlaceVec.sandwich_cancel _ _ _ _ _ _ _ _ _ (gram_inv_map_mul S) βS.inv_mul (gram_inv_map_mul T)
        βT.inv_mul
    refine ⟨cA D e • x', fun i j => ?_, ?_⟩
    · show cA D e * (cA D e * x' i j) = cA D e * x' i j
      rw [← mul_assoc, hc.1]
    · ext i j
      simp only [rdAdj, Matrix.map_apply, frMapAdj_smul_eq, GlobalTheory.DualPairCheck.cA_cA, hfx, Matrix.smul_apply,
        smul_eq_mul, map_mul, Matrix.of_apply, hN]
      rw [show φ (toEAf D e) = 1 from h1, one_mul]
  · intro x x' hx hx' h
    have hd : IsHalf (cA D e) (x - x') := fun i j => by
      show cA D e * (x i j - x' i j) = x i j - x' i j
      rw [mul_sub, hx i j, hx' i j]
    have h0 : frMapAdj S T βS βT (x - x') = 0 := by
      ext i j
      have e1 := congrFun (congrFun h i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT (x - x') i j) = 0 := by
        rw [frMapAdj_sub, Matrix.sub_apply, map_sub, e1, sub_self]
      have e3 := (hker _).1 e2
      have e4 := congrFun (congrFun (frMapAdj_half S T βS βT hd) i) j
      rw [Matrix.smul_apply, smul_eq_mul, e3] at e4
      rw [← e4, Matrix.zero_apply]
    have hf := frMapAdj_eq_zero S T βS βT h0
    have hinf := GlobalTheory.SplitScalar.half_fin hc hd
    ext i j
    refine sub_eq_zero.1 (GlobalTheory.SplitScalar.adele_ext ?_ ?_)
    · have := congrFun (congrFun hinf i) j
      rw [map_zero]; exact this
    · rw [map_zero]
      exact finPart_eq_zero_of_toEAf (congrFun (congrFun hf i) j)
  · intro x hx
    have hh := fun i j => congrFun (congrFun (frMapAdj_half S T βS βT hx) i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    constructor
    · intro hI'
      refine ⟨Matrix.of fun i j => ⟨φ (frMapAdj S T βS βT x i j), (hint _).1 (by rw [hh i j]; exact hI' i j)⟩, ?_⟩
      ext i j
      rfl
    · rintro ⟨z, hz⟩ i j
      have e1 := congrFun (congrFun hz i) j
      simp only [rdAdj, Matrix.map_apply] at e1
      have e2 : φ (frMapAdj S T βS βT x i j) ∈ v.adicCompletionIntegers D.host.F := by
        rw [e1]; exact (z i j).2
      rw [← hh i j]
      exact (hint _).2 e2
  · intro x z hI' hz
    ext i j
    have e1 := congrFun (congrFun hz i) j
    simp only [rdAdj, Matrix.map_apply] at e1
    simp only [Matrix.map_apply, redM, dif_pos (hI' i j)]
    exact hred ⟨_, hI' i j⟩ (z i j) e1.symm

end GlobalTheory.DownLift.ReadAdj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalfStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → (∀ m, ∃ x : WO S T, IsHalf (cA D e) x ∧ rdAdj S T βS βT φ x = m) ∧ (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → rdAdj S T βS βT φ x = rdAdj S T βS βT φ x' → x = x') ∧ (∀ x : WO S T, IsHalf (cA D e) x → (IsIntM (frMapAdj S T βS βT x) ↔ ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))) ∧ ∀ (x : WO S T) (z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v)), IsIntM (frMapAdj S T βS βT x) → rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → (redM PP (frMapAdj S T βS βT x)).map ι = z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)) := by
  first | exact @GlobalTheory.DownLift.ReadAdj.rdAdj_read | exact GlobalTheory.DownLift.ReadAdj.rdAdj_read | (intros; apply GlobalTheory.DownLift.ReadAdj.rdAdj_read <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensions
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

namespace GlobalTheory.TransportCoef

open Formalism.MainNotions.N (twistRep coefRep)
open ReciprocityTheory.Def (d0 d1 C1)

variable {O G : Type} [CommRing O] [Group G] {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M']
  [Module O M']

theorem rTensor_coefRep (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (X : Type) [AddCommGroup X] [Module O X] (g : G) (y : M ⊗[O] X) :
    LinearMap.rTensor X e (coefRep W X g y) = coefRep W' X g (LinearMap.rTensor X e y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul m x => rw [coefRep_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul, coefRep_tmul, he]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]

theorem twist_intertwine (W : Representation O G M) (W' : Representation O G M') (e : M →ₗ[O] M')
    (he : ∀ g x, e (W g x) = W' g (e x)) (χ : G →* Oˣ) (g : G) (x : M) :
    e (twistRep W χ g x) = twistRep W' χ g (e x) := by
  rw [twistRep_apply, twistRep_apply, map_smul, he]

variable [TopologicalSpace G]

section General

variable {P P' : Type} [AddCommGroup P] [Module O P] [AddCommGroup P'] [Module O P']
  (π : Representation O G P) (π' : Representation O G P') (F : P →ₗ[O] P')
  (hF : ∀ g y, F (π g y) = π' g (F y))
include hF

theorem mem_Z1_comp {z : G → P} (hz : z ∈ Z1 π ⊤) : (fun g => F (z g)) ∈ Z1 π' ⊤ := by
  rw [Z1, Submodule.mem_inf] at hz ⊢
  obtain ⟨h1, h2⟩ := hz
  refine ⟨⟨h1.1.comp F, fun _ => Submodule.mem_top⟩, ?_⟩
  rw [LinearMap.mem_ker] at h2 ⊢
  funext x
  have := congrFun h2 x
  simp only [d1, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this ⊢
  rw [← hF, ← map_sub, ← map_add (f := _), this, map_zero]

theorem cob_comp {z : G → P} (S : Set G) (b : P) (hb : ∀ g ∈ S, z g = π g b - b) :
    ∀ g ∈ S, F (z g) = π' g (F b) - F b := by
  intro g hg
  rw [hb g hg, map_sub, hF]

theorem mem_B1_comp {z : G → P} (hz : z ∈ B1 π ⊤) : (fun g => F (z g)) ∈ B1 π' ⊤ := by
  rw [ReciprocityTheory.Def.B1, Submodule.mem_map] at hz ⊢
  obtain ⟨b, -, rfl⟩ := hz
  refine ⟨F b, Submodule.mem_top, ?_⟩
  funext g
  simp only [d0, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_sub, hF]

end General

end GlobalTheory.TransportCoef

namespace GlobalTheory.TransportCoef
open Formalism.MainNotions.N (twistRep coefRep)

theorem transport {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M') (he : ∀ g x, e (W g x) = W' g (e x)) :
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  intro χ X _ _ z z' hzz
  have he' : ∀ g x, e.symm (W' g x) = W g (e.symm x) := fun g x => by
    apply e.injective
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  let E := LinearEquiv.rTensor X e
  have hE : ∀ y, E y = LinearMap.rTensor X (e : M →ₗ[O] M') y := fun _ => rfl
  have hEs : ∀ y, E.symm y = LinearMap.rTensor X (e.symm : M' →ₗ[O] M) y := by
    intro y
    apply E.injective
    rw [LinearEquiv.apply_symm_apply, hE, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
    simp
  have key : ∀ g y, (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (twCoef W χ X g y) = twCoef W' χ X g (E y) := fun g y =>
    rTensor_coefRep (twistRep W χ⁻¹) (twistRep W' χ⁻¹) (e : M →ₗ[O] M')
      (twist_intertwine W W' (e : M →ₗ[O] M') he χ⁻¹) X g y
  have keys : ∀ g y, (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (twCoef W' χ X g y) = twCoef W χ X g (E.symm y) :=
    fun g y => by
      show E.symm _ = _
      rw [hEs, hEs]
      exact rTensor_coefRep (twistRep W' χ⁻¹) (twistRep W χ⁻¹) (e.symm : M' →ₗ[O] M)
        (twist_intertwine W' W (e.symm : M' →ₗ[O] M) he' χ⁻¹) X g y
  have keyc : ∀ g y, E (coefRep W X g y) = coefRep W' X g (E y) := fun g y =>
    rTensor_coefRep W W' (e : M →ₗ[O] M') he X g y
  have hz'f : z' = fun g => (E : M ⊗[O] X →ₗ[O] M' ⊗[O] X) (z g) := funext hzz
  have hzf : z = fun g => (E.symm : M' ⊗[O] X →ₗ[O] M ⊗[O] X) (z' g) := by
    funext g; show z g = E.symm (z' g); rw [hzz, LinearEquiv.symm_apply_apply]
  refine ⟨⟨fun hz => ?_, fun hz' => ?_⟩, ?_, ⟨fun hz => ?_, fun hz' => ?_⟩, fun I => ⟨?_, ?_⟩⟩
  · rw [hz'f]; exact mem_Z1_comp _ _ _ key hz
  · rw [hzf]; exact mem_Z1_comp _ _ _ keys hz'
  · intro hz hz' c hc
    refine ⟨E.prodCongr (LinearEquiv.refl O _), fun g x => ?_⟩
    obtain ⟨m, q⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [LinearEquiv.prodCongr_apply, Ea_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply,
      LinearEquiv.refl_apply, Ea_apply]
    simp only [Prod.mk.injEq, and_true]
    rw [map_add (f := _), map_smul, keyc, hzz]
  · rw [hz'f]; exact mem_B1_comp _ _ _ key hz
  · rw [hzf]; exact mem_B1_comp _ _ _ keys hz'
  · rintro ⟨b, hb⟩
    refine ⟨E b, fun g hg => ?_⟩
    rw [hzz]
    exact cob_comp _ _ _ key (I : Set G) b hb g hg
  · rintro ⟨b, hb⟩
    refine ⟨E.symm b, fun g hg => ?_⟩
    rw [hzf]
    exact cob_comp _ _ _ keys (I : Set G) b hb g hg

end GlobalTheory.TransportCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantIsoTransportCocyclesExtensionsStatement
open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivariantIso_transport_cocycles_extensions : ∀ {O G : Type} [CommRing O] [Group G] [TopologicalSpace G] {M M' : Type} [AddCommGroup M]
    [Module O M] [AddCommGroup M'] [Module O M'] (W : Representation O G M) (W' : Representation O G M')
    (e : M ≃ₗ[O] M'), (∀ g x, e (W g x) = W' g (e x)) →
    ∀ (χ : G →* Oˣ) (X : Type) [AddCommGroup X] [Module O X] (z : G → M ⊗[O] X) (z' : G → M' ⊗[O] X),
      (∀ g, z' g = LinearEquiv.rTensor X e (z g)) →
      (z ∈ Z1 (twCoef W χ X) ⊤ ↔ z' ∈ Z1 (twCoef W' χ X) ⊤) ∧
      (∀ (hz : z ∈ Z1 (twCoef W χ X) ⊤) (hz' : z' ∈ Z1 (twCoef W' χ X) ⊤) {c : O} (hc : ∀ x : X, c • x = 0),
        ∃ f : ((M ⊗[O] X) × (O ⧸ Ideal.span {c})) ≃ₗ[O] ((M' ⊗[O] X) × (O ⧸ Ideal.span {c})),
          ∀ g x, f (Ea W χ hc ⟨z, hz⟩ g x) = Ea W' χ hc ⟨z', hz'⟩ g (f x)) ∧
      (z ∈ B1 (twCoef W χ X) ⊤ ↔ z' ∈ B1 (twCoef W' χ X) ⊤) ∧
      ∀ I : Subgroup G, (∃ b, ∀ g ∈ I, z g = twCoef W χ X g b - b) ↔
        (∃ b', ∀ g ∈ I, z' g = twCoef W' χ X g b' - b') := by
  first | exact @GlobalTheory.TransportCoef.transport | exact GlobalTheory.TransportCoef.transport | (intros; apply GlobalTheory.TransportCoef.transport <;> assumption)
end
end
