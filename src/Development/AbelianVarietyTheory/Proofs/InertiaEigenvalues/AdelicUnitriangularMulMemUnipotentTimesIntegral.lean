module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinSeedDiscNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOneProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAinfMatrixFrobeniusGaloisEqs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteProjectiveModuleElementDescentEqualizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep

namespace GlobalTheory.CellDec

variable (E : Type) [Field E] [NumberField E] (n : ℕ)

abbrev NA : Subgroup (GA E n) := GlobalTheory.SmGL.unipB (Ad E) (Fin n)

def NE : Subgroup (GA E n) := (GlobalTheory.SmGL.unipB E (Fin n)).map (ratGL E n)

def compV (v : HeightOneSpectrum (𝓞 E)) : GA E n →* GL (Fin n) (v.adicCompletion E) :=
  GeneralLinearGroup.map ((pLoc E v).comp (pFin E))

def US (S : Finset (HeightOneSpectrum (𝓞 E))) : Subgroup (GA E n) :=
  ⨅ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), (GlobalTheory.LFun.KGL v (n := n)).comap (compV E n v)

def C0 (S : Finset (HeightOneSpectrum (𝓞 E))) : Set (GA E n) :=
  {g | ∃ u ∈ NA E n, ∃ k ∈ US E n S, g = u * k}

abbrev abelian₂ (S : Finset (HeightOneSpectrum (𝓞 E))) : Type :=
  {l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ) // ∀ v ∈ S, l v = 0}

variable {E}

def adl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m : HeightOneSpectrum (𝓞 E) →₀ ℤ) : (Af E)ˣ where
  val := ⟨fun v => ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.support.finite_toSet.compl_mem_cofinite] with v hv
    have hv : m v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hv, zpow_zero, Units.val_one]
    exact one_mem _⟩
  inv := ⟨fun v => ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E), by
    filter_upwards [m.support.finite_toSet.compl_mem_cofinite] with v hv
    have hv : m v = 0 := Finsupp.notMem_support_iff.mp hv
    rw [hv, neg_zero, zpow_zero, Units.val_one]
    exact one_mem _⟩
  val_inv := FiniteAdeleRing.ext E fun v => by
    change ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  inv_val := FiniteAdeleRing.ext E fun v => by
    change ((ϖ v ^ (-m v) : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : _) = 1
    rw [← Units.val_mul, ← _root_.zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

def tl (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : GA E n :=
  finGL E n (GlobalTheory.SmGL.diagT (Af E) (Fin n) fun i => adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))

def wtS (a : Fin n → ℤ) : ℤ := ∑ i : Fin n, ∑ j : Fin n, if i < j then a i - a j else 0

def dinv (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) : ℝ :=
  ∏ v ∈ l.support, (qV E v : ℝ) ^ wtS n (l v)

end GlobalTheory.CellDec

namespace GlobalTheory.CellDec
open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem diagT_conj_mem {R : Type} [CommRing R] (w : Fin n → Rˣ) {u : GL (Fin n) R}
    (hu : u ∈ GlobalTheory.SmGL.unipB R (Fin n)) :
    GlobalTheory.SmGL.diagT R (Fin n) w * u * (GlobalTheory.SmGL.diagT R (Fin n) w)⁻¹ ∈ GlobalTheory.SmGL.unipB R (Fin n) := by
  rw [← map_inv]
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB R).1 hu
  refine (GlobalTheory.SmGL.mem_unipB R).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h1 i j hij]
    simp
  · simp only [Units.val_mul, GlobalTheory.SmGL.val_diagT, Matrix.diagonal_mul, Matrix.mul_diagonal, h2 i]
    simp

theorem countable_places (F : Type) [Field F] [NumberField F] : Countable (HeightOneSpectrum (𝓞 F)) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have : Countable (Ideal (𝓞 F)) := by
    have hs : Function.Surjective (fun t : Finset (𝓞 F) => Ideal.span (t : Set (𝓞 F))) := fun I => by
      obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
      exact ⟨t, ht⟩
    exact hs.countable
  have hi : Function.Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) := fun v w h => HeightOneSpectrum.ext h
  exact hi.countable

instance countable_Lam (S : Finset (HeightOneSpectrum (𝓞 E))) : Countable (abelian₂ E n S) := by
  have := countable_places E
  exact Subtype.countable

theorem tl_eq_diagT (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ)) :
    tl n ϖ l = GlobalTheory.SmGL.diagT (Ad E) (Fin n) fun i => finId E (adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l)) := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_diagT]
  ext i j
  change (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - sFin E ((1 : Matrix (Fin n) (Fin n) (Af E)) i j) +
    sFin E ((GlobalTheory.SmGL.diagT (Af E) (Fin n) _ : Matrix (Fin n) (Fin n) (Af E)) i j) = _
  rw [GlobalTheory.SmGL.val_diagT]
  by_cases h : i = j
  · subst h; simp [finId, GlobalTheory.CuspRep.corner]
  · simp [h]

theorem tl_conj_mem (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    {u : GA E n} (hu : u ∈ NA E n) : tl n ϖ l * u * (tl n ϖ l)⁻¹ ∈ NA E n := by
  rw [tl_eq_diagT]; exact diagT_conj_mem _ hu

theorem adelicUnitriangular_mul_mem_unipotentTimesIntegral {S : Finset (HeightOneSpectrum (𝓞 E))} {u g : GA E n} (hu : u ∈ NA E n) (hg : g ∈ C0 E n S) :
    u * g ∈ C0 E n S := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  exact ⟨u * v, mul_mem hu hv, k, hk, (mul_assoc _ _ _).symm⟩

end GlobalTheory.CellDec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfTwoMem
noncomputable section

namespace GlobalTheory.BaseChangeExistsCompare

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Matrix

section Definite

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem emb_hD (S : HSpace E) (τ : E →+* ℂ) (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) (x : S.V) :
    τ (S.hD x x) = star (fun a => τ (S.frame.repr x a)) ⬝ᵥ
      (S.gram.map τ *ᵥ fun a => τ (S.frame.repr x a)) := by
  rw [HSpace.hD, hT_expand]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hτ, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, Matrix.map_apply,
    mul_assoc]
  rfl

theorem denseRange_emb [_root_.NumberField.IsTotallyComplex E] (τ : E →+* ℂ) : DenseRange τ := by
  rcases Complex.subfield_eq_of_closed (Subfield.isClosed_topologicalClosure τ.fieldRange) with h | h
  · exfalso
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : τ x ∈ τ.fieldRange.topologicalClosure :=
      Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    simp
  · have : closure (Set.range τ) = Set.univ := congrArg (fun K : Subfield ℂ => (K : Set ℂ)) h
    exact dense_iff_closure_eq.2 this

theorem closed_of_coords [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (τ : E →+* ℂ) {C : Set (Fin S.rank → ℂ)}
    (hC : IsClosed C) (h : ∀ x : S.V, (fun a => τ (S.frame.repr x a)) ∈ C) (y : Fin S.rank → ℂ) : y ∈ C := by
  have hd : DenseRange (Pi.map fun (_ : Fin S.rank) => (τ : E → ℂ)) :=
    DenseRange.piMap fun _ => denseRange_emb τ
  refine hd.induction_on y hC fun v => ?_
  have := h (S.frame.equivFun.symm v)
  have e : (fun a => τ (S.frame.repr (S.frame.equivFun.symm v) a)) =
      Pi.map (fun (_ : Fin S.rank) => (τ : E → ℂ)) v := by
    funext a
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rfl
  rwa [e] at this

theorem coords_ne_zero (S : HSpace E) (τ : E →+* ℂ) {x : S.V} (hx : x ≠ 0) :
    (fun a => τ (S.frame.repr x a)) ≠ 0 := by
  intro h
  apply hx
  rw [← S.frame.repr.map_eq_zero_iff]
  ext a
  simpa using congrFun h a

theorem continuous_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun y : Fin n → ℂ => (star y ⬝ᵥ (M *ᵥ y)).re := by
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem sig_pos_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (S.rank, 0) ↔ ∀ x : S.V, x ≠ 0 → 0 < (τ (S.hD x x)).re := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_pos _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, 0 ≤ (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re := fun y =>
      closed_of_coords S τ (isClosed_le continuous_const (continuous_quad (S.gram.map τ))) (fun x => by
        show (0 : ℝ) ≤ _
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hq : (S.sig τ).2 = 0 := by
      by_contra hq
      have h1 := hall (Q *ᵥ Pi.single (Sum.inr ⟨0, Nat.pos_of_ne_zero hq⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext (by simp only; omega) hq

theorem sig_neg_iff [_root_.NumberField.IsTotallyComplex E] (S : HSpace E) (hS : S.SigOK) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a)) :
    S.sig τ = (0, S.rank) ↔ ∀ x : S.V, x ≠ 0 → (τ (S.hD x x)).re < 0 := by
  constructor
  · intro h x hx
    have hs := hS τ
    rw [h] at hs
    have := Formalism.UG.P.stdform_sig_neg _ hs _ (coords_ne_zero S τ hx)
    rwa [Formalism.UG.P.stdform_Q_dot, ← emb_hD S τ hτ] at this
  · intro h
    have hall : ∀ y : Fin S.rank → ℂ, (star y ⬝ᵥ (S.gram.map τ *ᵥ y)).re ≤ 0 := fun y =>
      closed_of_coords S τ (isClosed_le (continuous_quad (S.gram.map τ)) continuous_const) (fun x => by
        show _ ≤ (0 : ℝ)
        rw [← emb_hD S τ hτ]
        rcases eq_or_ne x 0 with rfl | hx
        · simp [HSpace.hD]
        · exact (h x hx).le) y
    obtain ⟨-, Q, hQ⟩ := Formalism.UG.P.sig_data _ _ _ (hS τ)
    have hsum := sig_sum S hS τ
    have hp : (S.sig τ).1 = 0 := by
      by_contra hp
      have h1 := hall (Q *ᵥ Pi.single (Sum.inl ⟨0, Nat.pos_of_ne_zero hp⟩) 1)
      rw [Formalism.UG.P.sig_quad _ Q hQ] at h1
      simp [Pi.single_apply] at h1
      linarith
    exact Prod.ext hp (by simp only; omega)

end Definite

theorem unram_of_cm (D : D7) (hc : @CMData D.host.F D.host.E _ _ _ _ D.host.cmStar _) (w : PlE D.host) :
    Algebra.IsUnramifiedAt (𝓞 D.host.F) w.asIdeal := by
  letI := D.host.cmStar
  haveI := D.host.isCMField_hostE
  have hU : Algebra.Unramified (𝓞 D.host.F) (𝓞 D.host.E) :=
    Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
      obtain ⟨θ, t, ht, hθ⟩ := hc.cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv
          (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
        RingOfIntegers.ext ht.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 hU ⟨w.asIdeal, w.isPrime⟩

section Concl

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

end Concl

end GlobalTheory.BaseChangeExistsCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem ideal_dual_symm {A : Type} [CommRing A] (I : Ideal A) (f : Module.Dual A ↥I)
    (x y : ↥I) : f x * (y : A) = f y * (x : A) := by
  have h : (x : A) • y = (y : A) • x := Subtype.ext (by simp [mul_comm])
  have := congrArg f h
  simp only [map_smul, smul_eq_mul] at this
  rw [mul_comm (f x), ← this, mul_comm]

theorem invertible_ideal_eq_of_not_le_maximal_mul (A : Type) [CommRing A] (I N : Ideal A) :
    Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  intro hI hNI hm

  set c : Ideal A := N.colon I with hc
  have key : ∀ (f : Module.Dual A ↥I) (n : ↥I), (n : A) ∈ N → f n ∈ c := by
    intro f n hn
    rw [hc, Submodule.mem_colon]
    intro p hp
    rw [smul_eq_mul, ideal_dual_symm I f n ⟨p, hp⟩]
    exact N.mul_mem_left _ hn
  have hcTop : c = ⊤ := by
    by_contra hne
    obtain ⟨m, hmax, hcm⟩ := Ideal.exists_le_maximal c hne
    apply hm m hmax
    intro n hn
    obtain ⟨t, ht⟩ := hI.bijective.2 1
    have hall : ∀ t : Module.Dual A ↥I ⊗[A] ↥I, contractLeft A ↥I t * n ∈ m * I := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f x =>
        rw [contractLeft_apply, ideal_dual_symm I f x ⟨n, hNI hn⟩]
        exact Ideal.mul_mem_mul (hcm (key f ⟨n, hNI hn⟩ hn)) x.2
      | add s u hs hu => rw [map_add (f := _), add_mul]; exact Ideal.add_mem _ hs hu
    simpa [ht] using hall t
  apply le_antisymm hNI
  intro y hy
  have h1 : (1 : A) ∈ c := hcTop ▸ Submodule.mem_top
  rw [hc, Submodule.mem_colon] at h1
  simpa using h1 y hy

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvertibleIdealEqOfNotLeMaximalMulStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul : ∀ (A : Type) [CommRing A] (I N : Ideal A), Module.Invertible A ↥I → N ≤ I → (∀ m : Ideal A, m.IsMaximal → ¬ N ≤ m * I) → N = I := by
  first | exact @GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | exact GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul | (intros; apply GlobalTheory.invertible_ideal_eq_of_not_le_maximal_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.Prism.Rigid

theorem φ_mem_of_mem {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m) : D.φ x ∈ m := by
  rw [D.φ_eq]
  exact Ideal.add_mem _ (Ideal.pow_mem_of_mem _ hx _ hl) (Ideal.mul_mem_right _ _ hlm)

theorem φ_mem_sq {l : ℕ} (hl : 0 < l) {A : Type} [CommRing A] (D : Delta l A) {m : Ideal A}
    (hlm : (l : A) ∈ m) {x : A} (hx : x ∈ m ^ 2) : D.φ x ∈ m ^ 2 := by
  have h : (m ^ 2).map D.φ ≤ m ^ 2 := by
    rw [Ideal.map_pow, sq, sq]
    have hm : m.map D.φ ≤ m := Ideal.map_le_iff_le_comap.2 fun y hy => φ_mem_of_mem hl D hlm hy
    exact Ideal.mul_mono hm hm
  exact h (Ideal.mem_map_of_mem _ hx)

theorem map_I_eq (l : ℕ) [hl : Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B') :
    B.I.map f.f = B'.I := by
  have hl0 : 0 < l := hl.out.pos
  have hNI : B.I.map f.f ≤ B'.I := Ideal.map_le_iff_le_comap.2 fun a ha => f.f_I a ha
  refine GlobalTheory.T.eq_of_le_invertible_of_not_le_maximal_mul B'.A B'.I (B.I.map f.f) B'.inv hNI ?_
  intro m hm hN

  have hjac : Ideal.span {(l : B'.A)} ⊔ B'.I ≤ m := by
    haveI := B'.complete
    refine le_trans (IsAdicComplete.le_jacobson_bot (Ideal.span {(l : B'.A)} ⊔ B'.I)) ?_
    exact sInf_le ⟨bot_le, hm⟩
  have hlm : (l : B'.A) ∈ m := hjac (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _))
  have hIm : B'.I ≤ m := le_trans le_sup_right hjac
  have hN2 : B.I.map f.f ≤ m ^ 2 := by
    rw [sq]; exact le_trans hN (Ideal.mul_mono_right hIm)

  have hmap : B.I ⊔ B.I.map B.D.φ ≤ (m ^ 2).comap f.f := by
    refine sup_le (fun a ha => hN2 (Ideal.mem_map_of_mem _ ha)) ?_
    refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
    show f.f (B.D.φ a) ∈ m ^ 2
    rw [f.f_φ]
    exact φ_mem_sq hl0 B'.D hlm (hN2 (Ideal.mem_map_of_mem _ ha))
  have hl2 : (l : B'.A) ∈ m ^ 2 := by
    have := hmap B.l_mem
    simpa [map_natCast] using this
  exact (GlobalTheory.T.prime_not_mem_sq_and_delta_not_mem l B'.A B'.D m hm.ne_top hlm).1 hl2

end GlobalTheory.Prism.Rigid
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prism_hom_map_ideal_eq : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B B' : Obj l R) (f : Hom B B'), B.I.map f.f = B'.I := by
  first | exact @GlobalTheory.Prism.Rigid.map_I_eq | exact GlobalTheory.Prism.Rigid.map_I_eq | (intros; apply GlobalTheory.Prism.Rigid.map_I_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.Per.ResFinite

theorem adm12_elementDenominator : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  intro D l _ K K' hKK hle LL T hc
  have hT := D.locT l
  have hdr := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l (D.loc l) (D.locA l) hT K' LL T.V T.ρ hc).1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ).1 hc
  · intro τ a
    exact GlobalTheory.T.hodgeJumpMultiplicity_restrict_finite_ext l (D.loc l) (D.locA l) hT K' K LL hKK T.V T.ρ hdr τ a

end GlobalTheory.Per.ResFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumpsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_restrict_finite_extension_jumps : ∀ D : D7, Formalism.MainNotions.ElementDenominator.adm12 D := by
  first | exact @GlobalTheory.Per.ResFinite.adm12_elementDenominator | exact GlobalTheory.Per.ResFinite.adm12_elementDenominator | (intros; apply GlobalTheory.Per.ResFinite.adm12_elementDenominator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroup
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.SmallActs

theorem toZModPow_cycZ_eq_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (n : ℕ) (σ : G F Ω) (hσ : ∀ ζ : Ω, ζ ^ (l ^ n) = 1 → σ ζ = ζ) :
    PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l]) = 1 := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have : NeZero ((l : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero⟩
  have hN0 : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  have : NeZero (l ^ n) := ⟨hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ n)
  have hspec : σ ζ = ζ ^ (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val :=
    cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G F Ω) (Ω) σ) ζ hζ.pow_eq_one
  rw [hσ ζ hζ.pow_eq_one] at hspec
  set m := (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])).val with hm
  have heq' : (hζ.isUnit hN0).unit ^ m = (hζ.isUnit hN0).unit ^ 1 := Units.ext (by simpa using hspec.symm)
  have hu : IsPrimitiveRoot (hζ.isUnit hN0).unit (l ^ n) := IsPrimitiveRoot.coe_units_iff.mp (by simpa using hζ)
  rw [pow_eq_pow_iff_modEq, ← hu.eq_orderOf] at heq'
  rw [← ZMod.natCast_zmod_val (PadicInt.toZModPow n ((cycZ F Ω l σ : ℤ_[l]ˣ) : ℤ_[l])), ← hm,
    (ZMod.natCast_eq_natCast_iff _ _ _).2 heq', Nat.cast_one]

theorem map_eq_one {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {r : ℕ} (T : Matrix (Fin r) (Fin r) O)
    (h : ∀ a b, algebraMap O A ((T - 1) a b) = 0) : T.map (algebraMap O A) = 1 := by
  ext a b
  have := h a b
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [Matrix.map_apply, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem repOn_of_map_eq_one {Γ O A : Type} [Group Γ] [CommRing O] [CommRing A] [Algebra O A] {r : ℕ}
    (ρ : Γ →* GL (Fin r) O) (κ : Γ →* Aˣ) (Y : Type) [AddCommGroup Y] [Module A Y] (g : Γ)
    (h : (ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A) = 1) (m : Fin r → Y) :
    repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m := by
  change (((κ g : Aˣ) : A) • matAct ((ρ g : Matrix (Fin r) (Fin r) O).map (algebraMap O A))) m = _
  rw [h, matAct_one]
  rfl

theorem small_acts : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  intro D N X i s _ M L z hM hS A _ _ κ ρ hK hρ Y _ _ g hg
  have hT : ∀ g ∈ L, (Tmat i s g).map (algebraMap (X.O0 i) A) = 1 := fun g hg =>
    map_eq_one _ fun a b => hK _ (hS.2.2 g hg a b)
  have hc : PadicInt.toZModPow (nu X i + 1) ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) = 1 := by
    refine toZModPow_cycZ_eq_one (nu X i + 1) g fun ζ hζ => hS.2.1 g hg ζ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hM
    have e : 2 * X.l i ^ M = X.l i ^ (nu X i + 1) * (2 * X.l i ^ k) := by rw [hk, pow_add (X.l i) (nu X i + 1) k]; ring
    rw [e, pow_mul, hζ, one_pow]
  refine ⟨repOn_of_map_eq_one _ κ Y g (by rw [Tgl_coe]; exact hT g hg), repOn_of_map_eq_one _ κ Y g ?_, Units.ext hc⟩
  have hmem : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := by
    intro h
    have h2 := h.map (algebraMap (X.O0 i) (X.O i))
    rw [map_natCast] at h2
    exact X.O_l i h2
  have he : algebraMap (X.O0 i) A ((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) = 1 := by
    have h1 : ((cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ) : ℤ_[X.l i]) - 1 ∈
        RingHom.ker (PadicInt.toZModPow (nu X i + 1) : ℤ_[X.l i] →+* ZMod (X.l i ^ (nu X i + 1))) := by
      rw [RingHom.mem_ker, map_sub, hc, map_one, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at h1
    obtain ⟨c, h1⟩ := h1
    change algebraMap (X.O0 i) A (algebraMap ℤ_[X.l i] (X.O0 i) (cycZ D.host.E N.Om (X.l i) g : ℤ_[X.l i]ˣ)) = 1
    have h2 : algebraMap (X.O0 i) A ((X.l i : X.O0 i) ^ nu X i * (X.l i : X.O0 i)) = 0 :=
      hK _ (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hmem)
    rw [sub_eq_iff_eq_add.1 h1, map_add (f := _), map_add (f := _), map_one, map_one, map_mul, map_pow, map_natCast, pow_succ, map_mul, h2,
      zero_mul, zero_add]
  have hinv : (Tmat i s g)⁻¹ = Tmat i s g⁻¹ := by
    rw [← Tgl_coe, ← Tgl_coe, map_inv, Matrix.coe_units_inv]
  rw [hρ g, Tdual, hinv]
  ext a b
  have := congrFun (congrFun (hT g⁻¹ (L.inv_mem hg)) b) a
  rw [Matrix.map_apply] at this
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, he, one_mul, Matrix.transpose_apply, this,
    Matrix.one_apply, Matrix.one_apply]
  simp only [eq_comm]

end GlobalTheory.NewPrime.SmallActs

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedRepresentationKillsSmallSubgroupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_representation_kills_small_subgroup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M : ℕ) (L : Subgroup (GE N)) (z : GE N), nu X i + 1 ≤ M → Small2 i s M L z → ∀ (A : Type) [CommRing A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)), Kills i A → IsDual i s ρ → ∀ (Y : Type) [AddCommGroup Y] [Module A Y], ∀ g ∈ L, (∀ m, repOn (Tgl i s) κ Y g m = ((κ g : Aˣ) : A) • m) ∧ (∀ m, repOn ρ κ Y g m = ((κ g : Aˣ) : A) • m) ∧ cycMod D.host.E N.Om (X.l i) (nu X i + 1) g = 1 := by
  first | exact @GlobalTheory.NewPrime.SmallActs.small_acts | exact GlobalTheory.NewPrime.SmallActs.small_acts | (intros; apply GlobalTheory.NewPrime.SmallActs.small_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof
noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

theorem stepDeg_main : StepDeg := fun D _ => GlobalTheory.TypeDegOne.degree_one D

end GlobalTheory.Pass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProofStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof : StepDeg := by
  first | exact @GlobalTheory.Pass.stepDeg_main | exact GlobalTheory.Pass.stepDeg_main | (intros; apply GlobalTheory.Pass.stepDeg_main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainIUnion
noncomputable section

open MeasureTheory
open scoped ENNReal Pointwise Matrix

namespace GlobalTheory.ThetaUnfold

section Abstract

variable {G ι : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

theorem lintegral_unfold (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → ℝ≥0∞) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEMeasurable f μ) :
    ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫⁻ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : MeasurableConstSMul Γ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : MeasurableConstSMul Δ G := ⟨fun γ => measurable_const_mul (γ : G)⟩
  haveI : SMulInvariantMeasure Γ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) ∩ 𝓕' : Set G) = 𝓕' ∩ e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul]
    rw [and_comm]
    refine and_congr_right fun _ => ?_
    rw [he]
    simp [mul_assoc]
  calc ∫⁻ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∑' i, ∫⁻ g in 𝓕, f (r i * g) ∂μ :=
        lintegral_tsum fun i => (hm.comp_quasiMeasurePreserving
          (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
    _ = ∑' i, ∫⁻ g in r i • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [(measurePreserving_mul_left μ (r i)).setLIntegral_comp_emb
          (measurableEmbedding_mulLeft (r i)) f 𝓕]
        rfl
    _ = ∑' i, ∑' δ : Δ, ∫⁻ g in 𝓕' ∩ e (δ, i) • 𝓕, f g ∂μ := by
        refine tsum_congr fun i => ?_
        rw [h𝓕'.setLIntegral_eq_tsum' f (r i • 𝓕)]
        refine tsum_congr fun δ => ?_
        rw [hset]
        congr 1
        funext g
        exact hf _ (δ⁻¹).2 g
    _ = ∑' p : Δ × ι, ∫⁻ g in 𝓕' ∩ e p • 𝓕, f g ∂μ := by
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    _ = ∑' γ : Γ, ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ := e.tsum_eq (fun γ => ∫⁻ g in 𝓕' ∩ γ • 𝓕, f g ∂μ)
    _ = ∫⁻ g in 𝓕', f g ∂μ := (h𝓕.setLIntegral_eq_tsum f 𝓕').symm

theorem isFundamentalDomain_iUnion (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) : IsFundamentalDomain Δ (⋃ i, r i • 𝓕) μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  have hset : ∀ (δ : Δ) (i : ι), (δ • (r i • 𝓕) : Set G) = e (δ, i) • 𝓕 := by
    intro δ i
    ext x
    simp only [Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_inv]
    rw [he]
    simp [mul_assoc]
  refine ⟨.iUnion fun i => h𝓕.nullMeasurableSet.smul (r i), h𝓕.ae_covers.mono ?_, fun δ δ' hδ => ?_⟩
  · rintro x ⟨γ, hγ⟩
    refine ⟨(e.symm γ⁻¹).1⁻¹, Set.mem_iUnion.2 ⟨(e.symm γ⁻¹).2, ?_⟩⟩
    rw [← Set.mem_smul_set_iff_inv_smul_mem, hset, Prod.mk.eta, e.apply_symm_apply,
      Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact hγ
  · simp only [Function.onFun, Set.smul_set_iUnion, hset, AEDisjoint.iUnion_left_iff, AEDisjoint.iUnion_right_iff]
    exact fun i j => h𝓕.aedisjoint fun h => hδ (by simpa using congrArg Prod.fst (e.injective h))

theorem integral_unfold {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (μ : Measure G) [μ.IsMulLeftInvariant] (Γ Δ : Subgroup G) [Countable Γ]
    (r : ι → G) (e : Δ × ι ≃ Γ) (he : ∀ p, (e p : G) = p.1 * r p.2)
    {𝓕 𝓕' : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (h𝓕' : IsFundamentalDomain Δ 𝓕' μ)
    (f : G → V) (hf : ∀ δ ∈ Δ, ∀ g, f (δ * g) = f g) (hm : AEStronglyMeasurable f μ)
    (hfin : ∫⁻ g in 𝓕, ∑' i, ‖f (r i * g)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun i => ‖f (r i * g)‖) ∧ IntegrableOn (fun g => ∑' i, f (r i * g)) 𝓕 μ ∧
      IntegrableOn f 𝓕' μ ∧ ∫ g in 𝓕, ∑' i, f (r i * g) ∂μ = ∫ g in 𝓕', f g ∂μ := by
  haveI : Countable ι := Function.Injective.countable (f := fun i => e (1, i))
    fun i j h => by simpa using congrArg Prod.snd (e.injective h)
  haveI : Countable Δ := Function.Injective.countable (f := fun δ => e (δ, (e.symm 1).2))
    fun i j h => by simpa using congrArg Prod.fst (e.injective h)
  haveI : SMulInvariantMeasure Δ G μ := ⟨fun γ s _ => measure_preimage_mul μ (γ : G) s⟩
  have hS := isFundamentalDomain_iUnion μ Γ Δ r e he h𝓕
  have hf' : ∀ (δ : Δ) (g : G), f (δ • g) = f g := fun δ g => hf δ δ.2 g
  have hmi : ∀ i, AEStronglyMeasurable (fun g => f (r i * g)) (μ.restrict 𝓕) := fun i =>
    (hm.comp_quasiMeasurePreserving (measurePreserving_mul_left μ (r i)).quasiMeasurePreserving).restrict
  have hI : IntegrableOn f 𝓕' μ := ⟨hm.restrict, by
    have := lintegral_unfold μ Γ Δ r e he h𝓕 h𝓕' (fun g => ‖f g‖ₑ) (fun δ h g => by rw [hf δ h]) hm.enorm
    exact lt_top_iff_ne_top.2 (this ▸ hfin)⟩
  have hr : ∀ i, (r i • 𝓕 : Set G) = e (1, i) • 𝓕 := fun i => by
    rw [Subgroup.smul_def, he]; simp
  refine ⟨?_, ⟨AEStronglyMeasurable.tsum hmi, ?_⟩, hI, ?_⟩
  · filter_upwards [ae_lt_top' (AEMeasurable.tsum fun i => (hmi i).enorm) hfin] with g hg
    have := ENNReal.summable_toReal hg.ne
    simpa using this
  · exact lt_of_le_of_lt (lintegral_mono fun x => enorm_tsum_le_tsum_enorm) hfin.lt_top
  · rw [integral_tsum hmi (by rwa [← lintegral_tsum fun i => (hmi i).enorm]), h𝓕'.setIntegral_eq hS hf',
      integral_iUnion_ae (fun i => h𝓕.nullMeasurableSet.smul (r i))
        (fun i j hij => by
          simp only [Function.onFun, hr]
          exact h𝓕.aedisjoint fun h => hij (by simpa using congrArg Prod.snd (e.injective h)))
        ((h𝓕'.integrableOn_iff hS hf').1 hI)]
    refine tsum_congr fun i => ?_
    exact ((measurePreserving_mul_left μ (r i)).setIntegral_image_emb (measurableEmbedding_mulLeft (r i)) f 𝓕).symm

end Abstract

section Concrete

open GlobalTheory.CuspRep

variable {E : Type} [Field E] {a : ℕ}

theorem exists_vecMul_eq {v ξ : Fin a → E} (hv : v ≠ 0) (hξ : ξ ≠ 0) :
    ∃ γ : GL (Fin a) E, v ᵥ* (γ : Matrix (Fin a) (Fin a) E) = ξ := by
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq
    ((LinearEquiv.toSpanNonzeroSingleton E _ v hv).symm.trans (LinearEquiv.toSpanNonzeroSingleton E _ ξ hξ))
  have h1 := hg ⟨v, Submodule.mem_span_singleton_self v⟩
  rw [← LinearEquiv.toSpanNonzeroSingleton_one E _ v hv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply, LinearEquiv.toSpanNonzeroSingleton_one,
    LinearEquiv.toSpanNonzeroSingleton_one] at h1
  set A := LinearMap.toMatrix' g.toLinearMap
  set B := LinearMap.toMatrix' g.symm.toLinearMap
  have hAB : A * B = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  have hBA : B * A = 1 := by rw [← LinearMap.toMatrix'_comp]; simp
  refine ⟨⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, hBA, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hAB, Matrix.transpose_one]⟩, ?_⟩
  change v ᵥ* Aᵀ = ξ
  rw [Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec]
  first | exact h1 | exact h1.symm

variable [NumberField E]

theorem vecMul_ratGL_mul (ξ : Fin a → E) (γ : GL (Fin a) E) (g : GA E a) :
    (algebraMap E (Ad E) ∘ ξ) ᵥ* (ratGL E a γ * g).val = (algebraMap E (Ad E) ∘ (ξ ᵥ* γ.val)) ᵥ* g.val := by
  rw [Units.val_mul, ← Matrix.vecMul_vecMul]
  congr 1
  ext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ratGL, Matrix.vecMul, dotProduct, map_sum]

theorem ratGL_injective : Function.Injective (ratGL E a) := fun _ _ h => by
  ext i j
  exact NumberField.AdeleRing.algebraMap_injective _ E
    (congrArg (fun z : GA E a => (z : Matrix (Fin a) (Fin a) (Ad E)) i j) h)

theorem countable_range_ratGL : Countable (ratGL E a).range := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin a) (Fin a) E) := inferInstanceAs (Countable (Fin a → Fin a → E))
  haveI : Countable (GL (Fin a) E) := Units.val_injective.countable
  exact (ratGL E a).rangeRestrict_surjective.countable

theorem exists_transversal {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)}
    (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v) :
    ∃ (γ : {ξ : Fin a → E // ξ ≠ 0} → GL (Fin a) E) (e : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} ≃ (ratGL E a).range),
      (∀ ξ, v ᵥ* (γ ξ).val = ξ.1) ∧ ∀ p, (e p : GA E a) = p.1 * ratGL E a (γ p.2) := by
  choose γ hγ using fun ξ : {ξ : Fin a → E // ξ ≠ 0} => exists_vecMul_eq hv ξ.2
  let φ : P.map (ratGL E a) × {ξ : Fin a → E // ξ ≠ 0} → (ratGL E a).range := fun p =>
    ⟨p.1 * ratGL E a (γ p.2), mul_mem (Subgroup.map_le_range _ _ p.1.2) ⟨_, rfl⟩⟩
  refine ⟨γ, Equiv.ofBijective φ ⟨?_, ?_⟩, hγ, fun _ => rfl⟩
  · rintro ⟨⟨_, δ, hδ, rfl⟩, ξ⟩ ⟨⟨_, δ', hδ', rfl⟩, ξ'⟩ h
    have h1 : δ * γ ξ = δ' * γ ξ' := ratGL_injective (by simpa only [map_mul] using congrArg Subtype.val h)
    have h2 : ξ = ξ' := Subtype.ext (by
      have := congrArg (fun x : GL (Fin a) E => v ᵥ* x.val) h1
      simpa only [Units.val_mul, ← Matrix.vecMul_vecMul, (hP _).1 hδ, (hP _).1 hδ', hγ] using this)
    subst h2
    obtain rfl := mul_right_cancel h1
    rfl
  · rintro ⟨_, x, rfl⟩
    have h0 : v ᵥ* x.val ≠ 0 := fun h => hv (by
      have := congrArg (· ᵥ* (x⁻¹).val) h
      simpa only [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one, Matrix.zero_vecMul] using this)
    have h1 : x * (γ ⟨_, h0⟩)⁻¹ ∈ P := (hP _).2 (by
      have h2 : v ᵥ* (γ ⟨_, h0⟩).val = v ᵥ* x.val := hγ _
      generalize γ ⟨_, h0⟩ = y at h2 ⊢
      rw [Units.val_mul, ← Matrix.vecMul_vecMul, ← h2, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one])
    refine ⟨⟨⟨_, _, h1, rfl⟩, ⟨_, h0⟩⟩, Subtype.ext ?_⟩
    change ratGL E a _ * ratGL E a _ = _
    rw [← map_mul, inv_mul_cancel_right]

section Stabiliser

variable [MeasurableSpace (GA E a)] [MeasurableMul (GA E a)] (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]
  {v : Fin a → E} (hv : v ≠ 0) {P : Subgroup (GL (Fin a) E)} (hP : ∀ γ, γ ∈ P ↔ v ᵥ* γ.val = v)
  {𝓕 𝓕' : Set (GA E a)} (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ)
  (h𝓕' : IsFundamentalDomain (P.map (ratGL E a)) 𝓕' μ)

include hv hP h𝓕 h𝓕'

theorem lintegral_tsum_vecMul (F : GA E a → (Fin a → Ad E) → ℝ≥0∞) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ) :
    ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫⁻ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := lintegral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

theorem integral_tsum_vecMul {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    (F : GA E a → (Fin a → Ad E) → V) (hF : ∀ γ g y, F (ratGL E a γ * g) y = F g y)
    (hm : AEStronglyMeasurable (fun g : GA E a => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) μ)
    (hfin : ∫⁻ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ g ∂μ.restrict 𝓕, Summable fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)‖) ∧
    IntegrableOn (fun g => ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val)) 𝓕 μ ∧
    IntegrableOn (fun g => F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val)) 𝓕' μ ∧
    ∫ g in 𝓕, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, F g ((algebraMap E (Ad E) ∘ ξ.1) ᵥ* g.val) ∂μ =
      ∫ g in 𝓕', F g ((algebraMap E (Ad E) ∘ v) ᵥ* g.val) ∂μ := by
  haveI := countable_range_ratGL (E := E) (a := a)
  obtain ⟨γ, e, hγ, he⟩ := exists_transversal hv hP
  have := integral_unfold μ _ _ (fun ξ => ratGL E a (γ ξ)) e he h𝓕 h𝓕' _
    (by rintro _ ⟨δ, hδ, rfl⟩ g; simp only [vecMul_ratGL_mul, hF, (hP _).1 hδ]) hm
    (by simpa only [vecMul_ratGL_mul, hF, hγ] using hfin)
  simpa only [vecMul_ratGL_mul, hF, hγ] using this

end Stabiliser

end Concrete

end GlobalTheory.ThetaUnfold
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionZeroOnePropertiesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x y : Disc l (0 : Wq l bk.a) 1, ‖x * y‖ = ‖x‖ * ‖y‖) ∧ (∀ x : Disc l (0 : Wq l bk.a) 1, ‖x‖ ≤ 1 → ∃ w, x = toDisc l (0 : Wq l bk.a) 1 w) ∧ Function.Injective (toDisc l (0 : Wq l bk.a) 1) ∧ ∀ w : Wq l bk.a, IsUnit w → ‖toDisc l (0 : Wq l bk.a) 1 w‖ = 1 := by
  first | exact @GlobalTheory.BSP.disc_zero_one | exact GlobalTheory.BSP.disc_zero_one | (intros; apply GlobalTheory.BSP.disc_zero_one <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem delta_add_sub_mem_pow : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A)
    (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  intro l _ A _ D J hl n x y hy
  have hy' : y ∈ J ^ n := Ideal.pow_le_pow_right (Nat.le_succ n) hy
  have hδ : D.δ y ∈ J ^ n := GlobalTheory.T.delta_mem_ideal_pow_of_mem_pow_succ l A D J hl n y hy
  rw [D.δ_add x y]
  have e : D.δ x + D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) - D.δ x
      = D.δ y - ∑ k ∈ Finset.Ioo 0 l, ((l.choose k / l : ℕ) : A) * x ^ k * y ^ (l - k) := by ring
  rw [e]
  refine Ideal.sub_mem _ hδ (Ideal.sum_mem _ fun k hk => ?_)
  have hk' : 0 < l - k := Nat.sub_pos_of_lt (Finset.mem_Ioo.1 hk).2
  have : y ^ (l - k) ∈ J ^ n := by
    obtain ⟨m, hm⟩ : ∃ m, l - k = m + 1 := ⟨l - k - 1, by omega⟩
    rw [hm, pow_succ]
    exact Ideal.mul_mem_left _ _ hy'
  exact Ideal.mul_mem_left _ _ this

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeltaAddSubMemPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.delta_add_sub_mem_pow_of_mem_pow_succ : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (J : Ideal A), (l : A) ∈ J → ∀ (n : ℕ) (x : A), ∀ y ∈ J ^ (n + 1), D.δ (x + y) - D.δ x ∈ J ^ n := by
  first | exact @GlobalTheory.BSP.delta_add_sub_mem_pow | exact GlobalTheory.BSP.delta_add_sub_mem_pow | (intros; apply GlobalTheory.BSP.delta_add_sub_mem_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCover
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCover
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

noncomputable def matCoordMap {A B : Type} [CommRing A] [CommRing B] {d : ℕ} (q : A →+* B)
    (M : Matrix (Fin d) (Fin d) B) : (Fin d → A) →ₛₗ[q] (Fin d → B) where
  toFun z := M.mulVec fun i => q (z i)
  map_add' x y := by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp
  map_smul' a x := by
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp

theorem Eval.effective_of_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  intro l _ K bk d S B C N _ _ V h f hc
  obtain ⟨D, p, q, hpo⟩ := hc.stable.po C h
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.prism_cover_injective_and_descent l _ B C h hc
  haveI := V.fin
  haveI := V.proj
  have hcomm : p.f.comp h.f = q.f.comp h.f := congrArg Hom.f hpo.comm
  have key := GlobalTheory.T.finite_projective_module_element_descent_equalizer B.A C.A D.A h.f p.f q.f hcomm hinj (hrange D p q hpo) N (Fin d → C.A) (Fin d → D.A)
    (V.v h f) (matCoordMap p.f 1) (matCoordMap q.f (S.ε (p.comp f) (q.comp f))) (V.v (p.comp h) (p.comp f))
    (V.bc h f) (V.bc (p.comp h) (p.comp f))
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (1 : Matrix (Fin d) (Fin d) D.A).mulVec fun i => p.f (V.v h f x i)
      rw [Matrix.one_mulVec]
      funext i
      exact V.v_nat p h f x i)
    (fun x => by
      change V.v (p.comp h) (p.comp f) x = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (V.v h f x i)
      have e : ∀ a a' : Hom B D, a = a' → V.v a (q.comp f) x = V.v a' (q.comp f) x := by
        intro a a' e; subst e; rfl
      rw [V.v_ε (p.comp h) (p.comp f) (q.comp f) x, e _ _ hpo.comm]
      congr 1
      funext i
      exact V.v_nat q h f x i)
  refine ⟨key.1, fun z hz => key.2 z ?_⟩
  change (1 : Matrix (Fin d) (Fin d) D.A).mulVec (fun i => p.f (z i)) =
    (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)
  rw [Matrix.one_mulVec]
  exact hz D p q hpo.comm

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_and_range_of_prism_cover : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (B C : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (V : Eval S B N) (h : Hom B C) (f : Hom bk.prism C), Cover h → Function.Injective (V.v h f) ∧ ∀ z : Fin d → C.A, (∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h → (fun i => p.f (z i)) = (S.ε (p.comp f) (q.comp f)).mulVec fun i => q.f (z i)) → ∃ y, V.v h f y = z := by
  first | exact @GlobalTheory.BSP.Eval.effective_of_cover | exact GlobalTheory.BSP.Eval.effective_of_cover | (intros; apply GlobalTheory.BSP.Eval.effective_of_cover <;> assumption)
end
end
