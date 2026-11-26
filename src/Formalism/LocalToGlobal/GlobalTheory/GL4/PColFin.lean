module

public import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
public import Formalism.LocalToGlobal.GlobalTheory.GL4.PTenFrames

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.GL4.PColLoc
open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

structure ZBasis {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) where
  J0 : Type
  [fin : Fintype J0]
  [dec : DecidableEq J0]
  bZ : J0 → MvPolynomial (ι × Fin n × Fin n) ℤ
  span_eq : Submodule.span ℤ (Set.range bZ) = Submodule.span ℤ
    {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f}
  li : ∀ (F : Type) [Field F] [CharZero F], LinearIndependent F fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)
  span_F : ∀ (F : Type) [Field F] [CharZero F],
    Submodule.span F (Set.range fun i => MvPolynomial.map (Int.castRingHom F) (bZ i)) = VV F lam

attribute [instance] ZBasis.fin ZBasis.dec

namespace ZBasis

variable {ι : Type} [Fintype ι] {n : ℕ} {lam : ι → DomWeight n} (Z : ZBasis lam)

def basis (F : Type) [Field F] [CharZero F] : Basis Z.J0 F (VV F lam) :=
  (Basis.span (Z.li F)).map (LinearEquiv.ofEq _ _ (Z.span_F F))

theorem basis_coe (F : Type) [Field F] [CharZero F] (i : Z.J0) :
    ((Z.basis F i : VV F lam) : Pol F ι n) = MvPolynomial.map (Int.castRingHom F) (Z.bZ i) := by
  simp only [basis, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]

end ZBasis

section Gen

variable {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_repr [NumberField K] (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) (i : J0) (c : Cl) :
    (sumBasis coE BK).repr x (i, c) = BK.repr (coE x c) i := by
  unfold sumBasis
  rw [Basis.repr_reindex_apply, Basis.map_repr]
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_symm]
  rfl

theorem mem_span_sumBasis [NumberField K] (R : Subring K) (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (x : V) :
    x ∈ Submodule.span R (Set.range (sumBasis coE BK)) ↔ ∀ c, coE x c ∈ Submodule.span R (Set.range BK) := by
  simp only [Basis.mem_span_iff_repr_mem, Prod.forall, sumBasis_repr]
  exact forall_comm

end Gen

section Rec

variable (D : D7)

theorem int_mem_intW (w : D.what₂.places.Pl) (o : 𝓞 D.what₂.LL) : (o : D.what₂.LL) ∈ intW D.what₂.places w :=
  (D.val_nonneg_iff w _).2 ((D.plEq w).valuation_le_one o)

theorem mem_localization_latticeOf_iff (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] {J : Type} (f : J → V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ Submodule.span (intW D.what₂.places w) (Set.range f) := by
  have h0 : x ∈ localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) f) ↔ x ∈ locW D.what₂.places w (latOf (K := D.what₂.LL) f) :=
    (D.mem_locW_iff w _ x).symm
  rw [h0]
  unfold locW
  have : Submodule.span (intW D.what₂.places w) ((latOf (K := D.what₂.LL) f : Submodule (𝓞 D.what₂.LL) V) : Set V) =
      Submodule.span (intW D.what₂.places w) (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy => exact Submodule.subset_span hy
      | zero => exact Submodule.zero_mem _
      | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
      | smul o y _ hy =>
        have : o • y = (⟨(o : D.what₂.LL), int_mem_intW D w o⟩ : intW D.what₂.places w) • y := by
          rw [Subring.smul_def, ← algebraMap_smul D.what₂.LL o]
        rw [SetLike.mem_coe, this]
        exact Submodule.smul_mem _ _ hy
    · exact Submodule.span_mono Submodule.subset_span
  rw [this]

theorem mem_localization_iff_localizationAtPlace (w : D.what₂.places.Pl) {V : Type} [AddCommGroup V] [Module D.what₂.LL V]
    [Module (𝓞 D.what₂.LL) V] [IsScalarTower (𝓞 D.what₂.LL) D.what₂.LL V] (A : Submodule (𝓞 D.what₂.LL) V) (x : V) :
    x ∈ localization₂ (D.plEq w).asIdeal A ↔ x ∈ locW D.what₂.places w A := (D.mem_locW_iff w _ x).symm

variable {D}

theorem map_ten {n : ℕ} (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) :
    Formalism.MainNotions.flipTwoThree.ten (fun τ => MvPolynomial.map (Int.castRingHom D.what₂.LL) (f τ)) =
      MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) := by
  simp only [Formalism.MainNotions.flipTwoThree.ten, map_prod, MvPolynomial.map_rename]

theorem mem_intSpanAt_iff {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) (Z : ZBasis lam)
    (y : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL) :
    y ∈ IntSpanAt D w lam ↔ y ∈ Submodule.span (intW D.what₂.places w)
      (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
  constructor
  · intro hy
    unfold IntSpanAt at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨r, f, hr, hf, rfl⟩ := hy
      rw [map_ten]
      have h1 : Formalism.MainNotions.flipTwoThree.ten f ∈ Submodule.span ℤ (Set.range Z.bZ) := by
        rw [Z.span_eq]; exact Submodule.subset_span ⟨f, hf, rfl⟩
      have h2 : MvPolynomial.map (Int.castRingHom D.what₂.LL) (Formalism.MainNotions.flipTwoThree.ten f) ∈ Submodule.span (intW D.what₂.places w)
          (Set.range fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i)) := by
        generalize Formalism.MainNotions.flipTwoThree.ten f = q0 at h1 ⊢
        induction h1 using Submodule.span_induction with
        | mem q hq => obtain ⟨i, rfl⟩ := hq; exact Submodule.subset_span ⟨i, rfl⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add p q _ _ hp hq => rw [map_add (f := _)]; exact Submodule.add_mem _ hp hq
        | smul z q _ hq =>
          rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
          exact zsmul_mem hq z
      exact Submodule.smul_mem _ (⟨r, hr⟩ : intW D.what₂.places w) h2
    | zero => exact Submodule.zero_mem _
    | add p q _ _ hp hq => exact Submodule.add_mem _ hp hq
    | neg p _ hp => exact Submodule.neg_mem _ hp
  · intro hy
    have hsm : ∀ (r : intW D.what₂.places w) (q : MvPolynomial (D.what₂.Tau × Fin n × Fin n) D.what₂.LL),
        q ∈ IntSpanAt D w lam → r • q ∈ IntSpanAt D w lam := by
      intro r q hq
      unfold IntSpanAt at hq ⊢
      induction hq using AddSubgroup.closure_induction with
      | mem y hy =>
        obtain ⟨r', f, hr', hf, rfl⟩ := hy
        refine AddSubgroup.subset_closure ⟨(r : D.what₂.LL) * r', f, mul_mem r.2 hr', hf, ?_⟩
        rw [Subring.smul_def, smul_smul]
      | zero => rw [smul_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [smul_add]; exact add_mem hp hq
      | neg p _ hp => rw [smul_neg]; exact neg_mem hp
    induction hy using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨i, rfl⟩ := hq
      have h1 : Z.bZ i ∈ Submodule.span ℤ
          {p | ∃ f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ, (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧ p = Formalism.MainNotions.flipTwoThree.ten f} := by
        rw [← Z.span_eq]; exact Submodule.subset_span ⟨i, rfl⟩
      show MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) ∈ IntSpanAt D w lam
      generalize Z.bZ i = q0 at h1 ⊢
      induction h1 using Submodule.span_induction with
      | mem q hq =>
        obtain ⟨f, hf, rfl⟩ := hq
        refine AddSubgroup.subset_closure ⟨1, f, one_mem _, hf, ?_⟩
        rw [one_smul, map_ten]
      | zero => rw [map_zero]; exact zero_mem _
      | add p q _ _ hp hq => rw [map_add (f := _)]; exact add_mem hp hq
      | smul z q _ hq =>
        rw [zsmul_eq_mul, map_mul, map_intCast, ← zsmul_eq_mul]
        exact zsmul_mem hq z
    | zero => exact zero_mem _
    | add p q _ _ hp hq => exact add_mem hp hq
    | smul r q _ hq => exact hsm r q hq

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
end

open Module NumberField IsDedekindDomain MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.HN Formalism.BasicNotions.SkeletonIndexLemmas Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions.flipTwoThree
open Formalism.LFunctionChainParameters.slopeLatticeData (FinPl)

section Alg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem actAll_eq_actP (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (p : Pol K ι n) :
    actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) p = actP lam g p := by
  unfold actAll actP detTwK detPow trAct Formalism.GradedWeylDivisibility.blockAct
  rw [LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]

def rhoEquiv (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) : VV K lam ≃ₗ[K] VV K lam :=
  LinearEquiv.ofLinearMap (rhoK lam g) (rhoK lam g⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rhoEquiv_apply (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) : rhoEquiv lam g y = rhoK lam g y := rfl

theorem rhoEquiv_symm_coe (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) (y : VV K lam) :
    (((rhoEquiv lam g).symm y : VV K lam) : Pol K ι n) =
      actAll lam (fun τ => ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)⁻¹) (y : Pol K ι n) := by
  show actP lam g⁻¹ (y : Pol K ι n) = _
  rw [← actAll_eq_actP]
  congr 1
  funext τ
  exact Matrix.GeneralLinearGroup.coe_inv (g τ)

theorem mem_span_subtype {P : Type} [AddCommGroup P] [Module K P] (R : Subring K) (U : Submodule K P) {J : Type} (b : J → U) (y : U) :
    y ∈ Submodule.span R (Set.range b) ↔ (y : P) ∈ Submodule.span R (Set.range fun i => (b i : P)) := by
  have h : (Submodule.span R (Set.range b)).map (U.subtype.restrictScalars R) =
      Submodule.span R (Set.range fun i => (b i : P)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [← h]
  constructor
  · intro hy; exact ⟨y, hy, rfl⟩
  · rintro ⟨z, hz, hzy⟩
    have : z = y := Subtype.ext hzy
    rwa [← this]

end Alg

section Gen

variable {K : Type} [Field K] [NumberField K] {V W : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
  {Cl : Type} [Fintype Cl] [DecidableEq Cl] {J0 : Type} [Fintype J0] [DecidableEq J0]

theorem sumBasis_twist (coE : V ≃ₗ[K] (Cl → W)) (BK : Basis J0 K W) (Φ : Cl → (W ≃ₗ[K] W)) :
    ⇑(sumBasis (coE.trans (LinearEquiv.piCongrRight fun c => (Φ c).symm)) BK) =
      fun j : J0 × Cl => coE.symm (Pi.single j.2 (Φ j.2 (BK j.1))) := by
  funext ⟨i, c⟩
  rw [sumBasis_apply]
  show coE.symm ((LinearEquiv.piCongrRight fun c => (Φ c).symm).symm (Pi.single c (BK i))) = _
  congr 1
  funext c'
  show (Φ c').symm.symm ((Pi.single c (BK i) : Cl → W) c') = _
  by_cases h : c' = c
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

end Gen

section Rec

variable {D : D7}

theorem exists_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) (hQ : Q.Good) {n : ℕ} (e : Q.ι ≃ Fin n) :
    ∃ γ, LocBasis D w Q e γ := by
  classical
  have hn : Module.finrank D.what₂.LL Q.V = n := by
    rw [Module.finrank_eq_card_basis Q.b, Fintype.card_congr e, Fintype.card_fin]
  obtain ⟨bK, hbK⟩ := exists_basis_locP (D.plEq w) hQ.2.1 hQ.2.2 hn
  refine ⟨(Q.b.reindex e).toMatrix bK, ?_, ?_⟩
  · have := (Q.b.reindex e).isUnit_det bK
    rwa [Basis.det_apply] at this
  · have hfam : (fun a : Fin n => ∑ i, (Q.b.reindex e).toMatrix bK i a • Q.b (e.symm i)) = bK := by
      funext a
      have := (Q.b.reindex e).sum_repr (bK a)
      simpa [Basis.toMatrix_apply, Basis.reindex_apply] using this
    rw [hfam]
    ext x
    rw [← mem_localization_iff_localizationAtPlace, ← hbK, mem_localization_latticeOf_iff]

theorem localization_eq_of_locBasis (w : D.what₂.places.Pl) (Q : HLat D.what₂.LL) {n : ℕ} (e : Q.ι ≃ Fin n)
    (γ : Matrix (Fin n) (Fin n) D.what₂.LL) (h : LocBasis D w Q e γ) :
    localization₂ (D.plEq w).asIdeal Q.L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun a : Fin n => ∑ i, γ i a • Q.b (e.symm i)) := by
  ext x
  rw [mem_localization_iff_localizationAtPlace, h.2, mem_localization_latticeOf_iff]

variable {u : D.what₂.Word} (CV : ColVal D u) (hTV : TSpan D.what₂.LL ((D.fm u).lam 0) = VV D.what₂.LL ((D.fm u).lam 0))

def coL : ((D.fm u).lat 0).V →ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearMap.pi fun c => LinearMap.codRestrict (VV D.what₂.LL ((D.fm u).lam 0)) ((LinearMap.proj c).comp CV.co)
    (fun x => hTV ▸ ((CV.co_range _).1 ⟨x, rfl⟩ c))

theorem coL_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coL CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl

theorem coL_bijective : Function.Bijective (coL CV hTV) := by
  constructor
  · intro x y h
    apply CV.co_inj
    funext c
    exact congrArg Subtype.val (congrFun h c)
  · intro F
    obtain ⟨x, hx⟩ := (CV.co_range (fun c => ((F c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)))).2
      (fun c => hTV.symm ▸ (F c).2)
    refine ⟨x, ?_⟩
    funext c
    apply Subtype.ext
    rw [coL_coe, hx]

def coE : ((D.fm u).lat 0).V ≃ₗ[D.what₂.LL] ((D.mem u).C.cls 0 → VV D.what₂.LL ((D.fm u).lam 0)) :=
  LinearEquiv.ofBijective (coL CV hTV) (coL_bijective CV hTV)

theorem coE_coe (x : ((D.fm u).lat 0).V) (c : (D.mem u).C.cls 0) :
    ((coE CV hTV x c : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) = CV.co x c := rfl


open Classical in
theorem localization_lattice_eq (Z : ZBasis ((D.fm u).lam 0)) (w : D.what₂.places.Pl)
    (g : (D.mem u).C.cls 0 → D.what₂.Tau → GL (Fin (D.R.N 0)) D.what₂.LL)
    (hg : ∀ c τ, LocBasis D w (CV.Q c τ) (CV.eQ c τ) (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) :
    localization₂ (D.plEq w).asIdeal ((D.fm u).lat 0).L =
      localization₂ (D.plEq w).asIdeal (latOf (K := D.what₂.LL) fun j : Z.J0 × (D.mem u).C.cls 0 =>
        (coE CV hTV).symm (Pi.single j.2 (rhoK ((D.fm u).lam 0) (g j.2) (Z.basis D.what₂.LL j.1)))) := by
  ext x
  have hf := sumBasis_twist (coE CV hTV) (Z.basis D.what₂.LL) (fun c => rhoEquiv ((D.fm u).lam 0) (g c))
  simp only [rhoEquiv_apply] at hf
  rw [mem_localization_iff_localizationAtPlace, CV.fin w (fun c τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)) hg x,
    mem_localization_latticeOf_iff, ← hf, mem_span_sumBasis]
  refine forall_congr' fun c => ?_
  rw [mem_span_subtype, mem_intSpanAt_iff w _ Z]
  have h1 : (fun i => ((Z.basis D.what₂.LL i : VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0))) =
      fun i => MvPolynomial.map (Int.castRingHom D.what₂.LL) (Z.bZ i) := funext fun i => Z.basis_coe D.what₂.LL i
  rw [h1]
  have h2 : ((((coE CV hTV).trans (LinearEquiv.piCongrRight fun c => (rhoEquiv ((D.fm u).lam 0) (g c)).symm)) x c :
      VV D.what₂.LL ((D.fm u).lam 0)) : Pol D.what₂.LL D.what₂.Tau (D.R.N 0)) =
      actAll ((D.fm u).lam 0) (fun τ => (g c τ : Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) D.what₂.LL)⁻¹) (CV.co x c) :=
    rhoEquiv_symm_coe _ _ _
  rw [h2]

end Rec

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
