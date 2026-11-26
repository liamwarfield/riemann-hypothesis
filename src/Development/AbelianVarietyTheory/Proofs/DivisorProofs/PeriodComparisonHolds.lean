module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsOfSpanAndTaylorClauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodsSpanDeRhamHomologyRankTwoG
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveCrystallineBaseChangeNilpotentThickenin

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussManinPeriodsHolds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PTaylor0
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseParamTaylorShift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorSumSubValueEqSumSqZero
set_option autoImplicit false

namespace GlobalTheory.PeriodFamily

theorem taylor_sum_sub_value_eq_sum_sqZero : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → ∀ {K : Type} (f : K → (I → ℂ) → ℂ), (∀ a, AnalyticAt ℂ (f a) 0) → ∃ n' : Fin r → K → D, (∀ j a, n' j a ∈ J) ∧ (∀ j a b, n' j a * n' j b = 0) ∧ ∀ a, GlobalTheory.PeriodFamily.taylor N (fun i ↦ ∑ j, n j i) (f a) - algebraMap ℂ D (f a 0) = ∑ j, n' j a := by
  intro I _ _ D _ _ J N hJ r
  induction r with
  | zero =>
    intro n _ _ K f _
    refine ⟨fun j ↦ j.elim0, fun j ↦ j.elim0, fun j ↦ j.elim0, fun a ↦ ?_⟩
    have h := taylor_sub_value_mem_span N (fun i ↦ ∑ j, n j i) (f a)
    have h0 : Ideal.span (Set.range (fun i ↦ ∑ j, n j i)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro x ⟨i, rfl⟩
      simp
    rw [h0, Ideal.mem_bot] at h
    rw [h]
    simp
  | succ r ih =>
    intro n hn hsq K f hf
    obtain ⟨n', h1, h2, h3⟩ := ih (fun j ↦ n j.succ) (fun j i ↦ hn _ _) (fun j i i' ↦ hsq _ _ _) f hf
    refine ⟨Fin.cons (fun a ↦ ∑ i, taylor N (fun i ↦ ∑ j : Fin r, n j.succ i)
      (fun z ↦ fderiv ℂ (f a) z (Pi.single i 1)) * n 0 i) n', ?_, ?_, fun a ↦ ?_⟩
    · intro j a
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        exact Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hn _ _)
      · simpa only [Fin.cons_succ] using h1 j a
    · intro j a b
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · simp only [Fin.cons_zero]
        rw [Finset.sum_mul_sum]
        refine Finset.sum_eq_zero fun i _ ↦ Finset.sum_eq_zero fun i' _ ↦ ?_
        rw [mul_mul_mul_comm, hsq, mul_zero]
      · simpa only [Fin.cons_succ] using h2 j a b
    · have he : (fun i ↦ ∑ j, n j i) = fun i ↦ (∑ j : Fin r, n j.succ i) + n 0 i := by
        funext i
        rw [Fin.sum_univ_succ, add_comm]
      have hle : Ideal.span (Set.range (fun i ↦ ∑ j : Fin r, n j.succ i) ∪ Set.range (n 0)) ≤ J := by
        rw [Ideal.span_le]
        rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact Ideal.sum_mem _ fun j _ ↦ hn _ _
        · exact hn _ _
      rw [he, taylor_add_of_mul_eq_zero N (fun i ↦ ∑ j : Fin r, n j.succ i) (n 0)
        (fun s hs ↦ hJ s fun a ↦ hle (hs a)) (hsq 0) (f a) (hf a), Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← h3 a]
      ring

end GlobalTheory.PeriodFamily
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnPer.close_paramTaylor_shift : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] {Λ : Type} [AddCommGroup Λ] (F : Fam I g Λ) (F₀ : Fam I₀ g Λ), (0 : I → ℂ) ∈ F.V → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D) (r : ℕ) (n : Fin r → I → D), (∀ j i, n j i ∈ J) → (∀ j i i', n j i * n j i' = 0) → (∀ i, t i = ∑ j, n j i) → ∀ (K : Charts F) (K₀ : Charts F₀) (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (Ta : Hol (K.W k) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀)) (Ta' : Hol (K.W k') →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀')), (∀ (h : Hol (K.W k)) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → (∀ (h : Hol (K.W k')) (p : Tot I₀ g) (hp : p ∈ K₀.W k₀'), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Ta' h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k₀'))) (Ta'.toRingHom.comp (Charts.sh h)) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀))).comp Ta).toRingHom) := by
  intro I I₀ _ _ _ g D _ _ Λ _ F F₀ h0 hτ J N hN t r n hn hnn ht K K₀ l k k' k₀ k₀' h h₀ hW Ta Ta' hTa hTa'
  have htJ : ∀ i, t i ∈ J := fun i ↦ by rw [ht]; exact J.sum_mem fun j _ ↦ hn j i
  have hnil : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0 := fun s ↦ hN _ fun a ↦ htJ _
  have hτa : AnalyticAt ℂ (F.τ l) 0 := F.hol l 0 h0
  obtain ⟨n', h1, h2, h3⟩ := GlobalTheory.PeriodFamily.taylor_sum_sub_value_eq_sum_sqZero J N hN r n hn hnn (fun (a : Fin g) z ↦ F.τ l z a)
    fun a ↦ analyticAt_pi_iff.1 hτa a
  have et : (fun i ↦ ∑ j, n j i) = t := funext fun i ↦ (ht i).symm
  rw [et] at h3
  obtain ⟨-, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hm : ∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2 + F.τ l 0) : Tot I g) ∈ K.W k := fun p hp ↦ K.maps h _ (hW p hp)
  refine GlobalTheory.AnPer.close_of_sliceTaylor J N hN t htJ r n' h1 h2 (K.W k) (K₀.W k₀') (fun p : Tot I₀ g ↦ p.2 + F.τ l 0)
    (fun p _ ↦ analyticAt_snd.add analyticAt_const) hm _ _ (fun f p hp ↦ ?_) fun f p hp ↦ ?_
  · refine (hTa' (Charts.sh h f) p hp).trans ?_
    have e : (fun z : I → ℂ ↦ (Charts.sh h f).fn (z, p.2)) =ᶠ[𝓝 0] fun z ↦ f.fn (z, p.2 + F.τ l z) := by
      have hc : Continuous (fun z : I → ℂ ↦ ((z, p.2) : Tot I g)) := by fun_prop
      filter_upwards [hc.continuousAt.eventually ((K.W k').isOpen.mem_nhds (hW p hp))] with z hz
        using Charts.fn_sh h f hz
    rw [hcongr _ _ e, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (F.τ l) p.2 hτa (f.analytic _ (hm p hp))]
    simp only [h3]
  · have hp' := K₀.maps h₀ p hp
    have e : ∀ x : D ⊗[ℂ] Hol (K₀.W k₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k₀')) (K₀.maps h₀)) x) =
        Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev (F₀.shift l p) hp')) (fun _ _ ↦ Commute.all _ _) x := fun x ↦ by
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul d c =>
        simp only [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply,
          Hol.ev_apply, Hol.fn_comap _ _ _ _ hp, AlgHom.id_apply]
    refine (e (Ta f)).trans ((hTa f _ hp').trans ?_)
    have e2 : (F₀.shift l p).2 = p.2 + F.τ l 0 := by simp only [Fam.shift, hτ]
    rw [e2, GlobalTheory.PeriodFamily.taylor_shear N t hnil f.fn (fun _ ↦ F.τ l 0) p.2 analyticAt_const (f.analytic _ (hm p hp))]
    simp only [hconst, sub_self]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHom
set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace TensorProduct GlobalTheory.AnPer

namespace GlobalTheory.TaylorHom

variable {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)}

theorem eventually_mem {w : Fin g → ℂ} (h : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    ∀ᶠ z in 𝓝 (0 : I → ℂ), ((z, w) : Tot I g) ∈ W := by
  have hc : Continuous fun z : I → ℂ ↦ ((z, w) : Tot I g) := by fun_prop
  exact hc.continuousAt.preimage_mem_nhds (W.isOpen.mem_nhds h)

theorem analyticAt_slice (h : Hol W) {w : Fin g → ℂ} (hw : (((0 : I → ℂ), w) : Tot I g) ∈ W) :
    AnalyticAt ℂ (fun z : I → ℂ ↦ h.fn (z, w)) 0 := by
  have hp : AnalyticAt ℂ (fun z : I → ℂ ↦ ((z, w) : Tot I g)) 0 :=
    analyticAt_id.prod analyticAt_const
  exact AnalyticAt.comp (g := h.fn) (f := fun z : I → ℂ ↦ ((z, w) : Tot I g)) (h.analytic _ hw) hp

def coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W) : Hol W₀ :=
  Hol.mk (fun p ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v) fun p hp ↦
    AnalyticAt.comp (g := fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) (f := Prod.snd)
      (GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v (h.analytic _ (hW p hp))).1 analyticAt_snd

theorem fn_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    {p : Tot I₀ g} (hp : p ∈ W₀) : (coef hW k v h).fn p = iteratedFDeriv ℂ k (fun z ↦ h.fn (z, p.2)) 0 v := by
  unfold coef
  exact Hol.fn_mk _ _ hp

theorem dw_coef (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (k : ℕ) (v : Fin k → I → ℂ) (h : Hol W)
    (a : Fin g) : dw a (coef hW k v h) = coef hW k v (dw a h) := by
  refine Hol.ext_fn fun p hp ↦ ?_
  have hH : AnalyticAt ℂ h.fn ((0 : I → ℂ), p.2) := h.analytic _ (hW p hp)
  obtain ⟨hG, hG'⟩ := GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv h.fn p.2 k v hH

  have hL : (dw a (coef hW k v h)).fn p =
      fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) p.2 (Pi.single a 1) := by
    rw [show dw a (coef hW k v h) =
        Hol.der ((0, Pi.single a 1) : Tot I₀ g) (coef hW k v h) from rfl, Hol.fn_der _ _ hp,
      Hol.fderiv_fn_congr (F := fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) _
        (fun q hq ↦ fn_coef hW k v h hq) hp]
    have hc := (hG.differentiableAt.hasFDerivAt.comp p (hasFDerivAt_snd (p := p))).fderiv
    rw [show (fun q : Tot I₀ g ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, q.2)) 0 v) =
        (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ h.fn (z, w)) 0 v) ∘ Prod.snd from rfl, hc]
    rfl
  have hR : (coef hW k v (dw a h)).fn p =
      iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1)) 0 v := by
    rw [fn_coef hW k v (dw a h) hp]
    have hev : (fun z : I → ℂ ↦ (dw a h).fn (z, p.2)) =ᶠ[𝓝 0]
        fun z ↦ fderiv ℂ h.fn (z, p.2) (0, Pi.single a 1) := by
      filter_upwards [eventually_mem (hW p hp)] with z hz
      exact Hol.fn_der _ _ hz
    exact congrFun (congrArg DFunLike.coe ((hev.iteratedFDeriv (𝕜 := ℂ) k).eq_of_nhds)) v
  rw [hL, hR]
  exact hG' _

variable [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D]

def poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W) : D ⊗[ℂ] Hol W₀ :=
  ∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I,
    ((k.factorial : ℂ)⁻¹ • ∏ a, t (s a)) ⊗ₜ[ℂ] coef hW k (fun a ↦ Pi.single (s a) 1) h

theorem ev_poly (hW : ∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) (N : ℕ) (t : I → D) (h : Hol W)
    (p : Tot I₀ g) (hp : p ∈ W₀) :
    Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
      (poly hW N t h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [poly, map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, Hol.ev_apply, fn_coef hW _ _ h hp, GlobalTheory.PeriodFamily.taylor]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]

theorem exists_taylor_algHom : ∀ {I I₀ : Type} [Fintype I] [DecidableEq I] [Fintype I₀] {g : ℕ} {D : Type} [CommRing D]
    [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) →
    ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot I₀ g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) →
    ∃ Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : Tot I₀ g) (hp : p ∈ W₀),
      Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _)
        (Ta h) = GlobalTheory.PeriodFamily.taylor N t fun z ↦ h.fn (z, p.2)) ∧
      ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h) := by
  intro I I₀ _ _ _ g D _ _ N t ht W W₀ hW

  have slice_eq : ∀ {p : Tot I₀ g} (_ : p ∈ W₀) {F : (I → ℂ) → ℂ} (x : Hol W),
      (∀ z, ((z, p.2) : Tot I g) ∈ W → x.fn (z, p.2) = F z) →
      GlobalTheory.PeriodFamily.taylor N t (fun z ↦ x.fn (z, p.2)) = GlobalTheory.PeriodFamily.taylor N t F := by
    intro p hp F x hx
    apply GlobalTheory.PeriodFamily.taylor_congr_germ
    filter_upwards [eventually_mem (hW p hp)] with z hz
    exact hx z hz
  have hconst : ∀ c : ℂ, poly hW N t (algebraMap ℂ (Hol W) c) = algebraMap ℂ (D ⊗[ℂ] Hol W₀) c := by
    intro c
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [ev_poly, AlgHom.commutes, slice_eq hp (F := fun _ ↦ c) _ fun z hz ↦ Hol.fn_algebraMap c hz,
      GlobalTheory.PeriodFamily.taylor_const_fun]
  have hadd : ∀ x y : Hol W, poly hW N t (x + y) = poly hW N t x + poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_add (f := _), ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) + y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_add x y hz,
      GlobalTheory.PeriodFamily.taylor_add_of_analyticAt N t _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  have hmul : ∀ x y : Hol W, poly hW N t (x * y) = poly hW N t x * poly hW N t y := by
    intro x y
    apply GlobalTheory.tensor_hol_ext_of_values W₀ D
    intro p hp
    rw [map_mul, ev_poly, ev_poly, ev_poly,
      slice_eq hp (F := fun z ↦ x.fn (z, p.2) * y.fn (z, p.2)) _ fun z hz ↦ Hol.fn_mul x y hz,
      GlobalTheory.PeriodFamily.taylor_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice x (hW p hp))
        (analyticAt_slice y (hW p hp))]
  refine ⟨{ toFun := poly hW N t
            map_one' := by simpa only [map_one] using hconst 1
            map_mul' := hmul
            map_zero' := by simpa only [map_zero] using hconst 0
            map_add' := hadd
            commutes' := hconst }, fun h p hp ↦ ev_poly hW N t h p hp, fun a h ↦ ?_⟩
  show poly hW N t (dw a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (poly hW N t h)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [poly, map_sum, LinearMap.lTensor_tmul]
  refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
  rw [← dw_coef]
  rfl

end GlobalTheory.TaylorHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenFib
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFib

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} (D : Type) [CommRing D]
  [Algebra ℂ D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀)

def inc (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) : CoefMap (algebraMap ℂ D) (O (dp0 ℂ) s₀) (K₀.Ten D) where
  G := r₀.functor
  α T := (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom
  naturality _ _ := rfl
  smul T a b := by
    subst hσ
    change ((1 : D) ⊗ₜ[ℂ] (a • (show T.C from b)) : T.ten D) = algebraMap ℂ D a • ((1 : D) ⊗ₜ[ℂ] (show T.C from b) : T.ten D)
    rw [tmul_smul, algebraMap_smul]

theorem ten_fib : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) (j₀ : ℂ →+* D₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' j₀ φ), (∀ a, io (j₀ a) = algebraMap ℂ D a) → ∀ (c : FirstDeRham s₀) (p : Λ → ℂ) (per : Λ →+ Hol F₀.V) (q : Λ →+ D), (∀ l, per l = algebraMap ℂ _ (p l)) → (∀ l, q l = algebraMap ℂ D (p l)) → r₀.coef.pull1 c = K₀.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (k.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ j₀ φ hφ k hj c p per q hper hq hc
  subst hφ
  let θ : (inc D r₀ hσ).G ⟶ (k.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom with
            commutes' := fun a ↦ by
              subst hσ
              change (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D) (algebraMap ℂ T.C a) =
                algebraMap D (T.ten D) (io (j₀ a))
              rw [AlgHom.commutes, hj, ← IsScalarTower.algebraMap_apply] }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun b ↦ congrArg (Ideal.Quotient.mk T.J) (by
            change (show T.C from b) = T.red π (1 ⊗ₜ (show T.C from b))
            rw [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul])
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat T.δ (T.tenδ π)
            (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom fun b hb ↦ by
              change T.red π (1 ⊗ₜ b) ∈ T.J
              rwa [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul]
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (r₀.obj T).x = (r₀.obj T).x ≫ 𝟙 X₀
            rw [Cris.spMap_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e := (inc D r₀ hσ).pullCohomologyOne_eq_of_natTrans _ θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp] at e
  refine e.symm.trans ?_
  obtain ⟨f, rfl⟩ := CatCoh.H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := CatCoh.H1.mk_eq_mk.1 hc
  refine CatCoh.H1.mk_eq_mk.2 ⟨fun T ↦ ((1 : D) ⊗ₜ[ℂ] (show T.C from G T) : T.ten D), ?_⟩
  funext T T' ψ
  have h1 := congrFun (congrFun (congrFun hG T) T') ψ
  have h2 : ((1 : D) ⊗ₜ[ℂ] ((show T'.C from G T') - ψ.φ (G T)) : T'.ten D) = (1 : D) ⊗ₜ[ℂ] (show T'.C from f.1 _ _ (r₀.functor.map ψ)) -
      (1 : D) ⊗ₜ[ℂ] (algebraMap (Hol F₀.V) T'.C (per ψ.deg)) := by
    rw [← tmul_sub]; exact congrArg _ h1
  refine (tmul_sub _ _ _).symm.trans (h2.trans ?_)
  congr 1
  change _ = algebraMap D (T'.ten D) (q ψ.deg)
  rw [hper, hq]
  exact (Algebra.TensorProduct.includeRight : T'.C →ₐ[ℂ] T'.ten D).commutes (p ψ.deg)

end GlobalTheory.AnPer.TenFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Functor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorComp
set_option autoImplicit false

noncomputable section

open TopologicalSpace TensorProduct

namespace GlobalTheory.AnPer

theorem Step.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (s : Step J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Step J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  obtain ⟨n, h1, h2, h3⟩ := s
  refine ⟨fun a ↦ (1 : D) ⊗ₜ[ℂ] n a, fun a ↦ hJ _ (h1 a), fun a b ↦ by simp [h2], fun f ↦ ?_⟩
  have key : ∀ x : D ⊗[ℂ] Hol W₀, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂ x =
      Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ x +
        ∑ a, Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁ (LinearMap.lTensor D (dw (W := W₀) a).toLinearMap x) *
          (1 : D) ⊗ₜ[ℂ] n a := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul d h =>
      have := h3 h
      simp only [RingHom.coe_coe] at this
      simp [this, tmul_add, tmul_sum]
    | add x y hx hy =>
      simp only [map_add (f := _), hx, hy, add_mul, Finset.sum_add_distrib]
      abel
  simpa [hT] using key (Ta f)

theorem Close.tensor_comp {I I₀ : Type} [Fintype I] [Fintype I₀] {g : ℕ} {D C : Type} [CommRing D] [Algebra ℂ D]
    [CommRing C] [Algebra ℂ C] {W : Opens (Tot I g)} {W₀ : Opens (Tot I₀ g)} (Ta : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀)
    (hT : ∀ a h, Ta (dw (W := W) a h) = LinearMap.lTensor D (dw (W := W₀) a).toLinearMap (Ta h))
    (J : Ideal C) (J' : Ideal (D ⊗[ℂ] C))
    (hJ : ∀ c ∈ J, (1 : D) ⊗ₜ[ℂ] c ∈ J') (ρ₁ ρ₂ : Hol W₀ →ₐ[ℂ] C)
    (h : Close J (ρ₁ : Hol W₀ →+* C) (ρ₂ : Hol W₀ →+* C)) :
    Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
      ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₂).comp Ta).toRingHom := by
  have key : ∀ ρ : Hol W₀ →+* C, Close J (ρ₁ : Hol W₀ →+* C) ρ → ∃ σ : Hol W₀ →ₐ[ℂ] C, (σ : Hol W₀ →+* C) = ρ ∧
      Close J' ((Algebra.TensorProduct.map (AlgHom.id ℂ D) ρ₁).comp Ta).toRingHom
        ((Algebra.TensorProduct.map (AlgHom.id ℂ D) σ).comp Ta).toRingHom := by
    intro ρ hρ
    induction hρ with
    | refl => exact ⟨ρ₁, rfl, Relation.ReflTransGen.refl⟩
    | @tail b c _ s ih =>
      obtain ⟨σ, rfl, ih⟩ := ih
      have hc : ∀ z : ℂ, c (algebraMap ℂ (Hol W₀) z) = algebraMap ℂ C z := by
        intro z
        obtain ⟨n, -, -, h3⟩ := s
        rw [h3]
        simp [Derivation.map_algebraMap]
      exact ⟨{ c with commutes' := hc }, rfl,
        Relation.ReflTransGen.tail ih (Step.tensor_comp Ta hT J J' hJ σ { c with commutes' := hc } s)⟩
  obtain ⟨σ, hσ, h'⟩ := key _ h
  obtain rfl : σ = ρ₂ := AlgHom.toRingHom_injective hσ
  exact h'

end GlobalTheory.AnPer
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFam

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀}
  {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) (hπ : IsNilpotent (RingHom.ker π))
  {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) (ν : K₀.K → K.K)
  (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D)
  (hc : ∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1)

def obj (T : K₀.Obj) : K.Obj where
  k := ν T.k
  C := T.ten D
  alg := ((algebraMap D (T.ten D)).comp τV).toAlgebra
  J := T.tenJ π
  nil := T.tenJ_nil π hπ
  ρ := ((Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc).comp (Ta T.k)).toRingHom
  ρ_cst f := by
    change Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc (Ta T.k (K.cst (ν T.k) f)) = τV f ⊗ₜ[ℂ] (1 : T.C)
    rw [hc, Algebra.TensorProduct.map_tmul, map_one]
    rfl

variable (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k))
  (hd : ∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h))
  (hcl : ∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom))


include hd hcl in
theorem close {T T' : K₀.Obj} (f : T ⟶ T') :
    Close (T'.tenJ π) ((obj π hπ K ν Ta τV hc T').ρ.comp (Charts.sh (hν _ _ _ (Charts.Hom.le f))))
      ((Charts.Hom.ten D f : T.ten D →+* T'.ten D).comp (obj π hπ K ν Ta τV hc T).ρ) := by
  have h1 := (hcl _ _ _ (Charts.Hom.le f)).map (J' := T'.tenJ π)
    (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom (fun c hc' ↦ by
      have : (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W T'.k)) ≤
          (T'.tenJ π).comap (Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc).toRingHom :=
        Ideal.map_le_iff_le_comap.2 fun d hd' ↦ by
          change T'.red π (d ⊗ₜ T'.ρc 1) ∈ T'.J
          rw [Charts.Obj.red_tmul, (RingHom.mem_ker).1 hd', map_zero, zero_mul]
          exact T'.J.zero_mem
      exact this hc')
  have h2 := GlobalTheory.AnPer.Close.tensor_comp (Ta T.k) (hd T.k) T'.J (T'.tenJ π) (fun c hc' ↦ by
      change T'.red π (1 ⊗ₜ c) ∈ T'.J
      rw [Charts.Obj.red_tmul]
      exact T'.J.mul_mem_left _ hc')
    (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k)) (K₀.maps (Charts.Hom.le f))))
    ((Charts.Hom.φc f).comp T.ρc) f.close
  have e1 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) T'.ρc
      (Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f))) x) = Algebra.TensorProduct.map (AlgHom.id ℂ D)
        (T'.ρc.comp (Hol.comap (F₀.shift f.deg) (F₀.shift_analytic f.deg (K₀.base T'.k))
        (K₀.maps (Charts.Hom.le f)))) x := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have e2 : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), Algebra.TensorProduct.map (AlgHom.id ℂ D) ((Charts.Hom.φc f).comp T.ρc) x =
      Charts.Hom.ten D f (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) := fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul d c => rfl
  have tr : ∀ {W : Opens (Tot I g)} {C : Type} [CommRing C] {J : Ideal C} {a b b' c c' : Hol W →+* C},
      Close J a b → Close J b' c → (∀ h, b h = b' h) → (∀ h, c h = c' h) → Close J a c' := by
    intro W C _ J a b b' c c' p q e e'
    obtain rfl : b = b' := RingHom.ext e
    obtain rfl : c = c' := RingHom.ext e'
    exact Relation.ReflTransGen.trans p q
  exact tr h1 h2 (fun h ↦ e1 (Ta T.k h)) (fun h ↦ e2 (Ta T.k h))

def functor : K₀.Obj ⥤ K.Obj where
  obj := obj π hπ K ν Ta τV hc
  map {T T'} f :=
    { φ := { (Charts.Hom.ten D f : T.ten D →+* T'.ten D) with commutes' := fun d ↦ (Charts.Hom.ten D f).commutes (τV d) }
      deg := f.deg
      le := hν _ _ _ (Charts.Hom.le f)
      mem := fun _ h ↦ Charts.Hom.ten_mem π f h
      close := close π hπ K ν Ta τV hc hν hd hcl f }
  map_id T := Charts.hom_ext (fun b ↦ mp_id (K₀.Ten D) T b) rfl
  map_comp f f' := Charts.hom_ext (fun b ↦ mp_comp (K₀.Ten D) f f' b) rfl

def coef : CoefMap τV K.Oc (K₀.Ten D) where
  G := functor π hπ K ν Ta τV hc hν hd hcl
  α T := RingHom.id (T.ten D)
  naturality _ _ := rfl
  smul T b c := (Algebra.smul_def (A := T.ten D) (τV b) c).symm

theorem main : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) {I : Type} [Fintype I] {F : Fam I g Λ} (K : Charts F) {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (r : Real K s σ) (ν : K₀.K → K.K) (hν : ∀ l k' k, K₀.le l k' k → K.le l (ν k') (ν k)) (Ta : ∀ k, Hol (K.W (ν k)) →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k)) (τV : Hol F.V →+* D), (∀ k f, Ta k (K.cst (ν k) f) = τV f ⊗ₜ[ℂ] 1) → (∀ k a h, Ta k (dw (W := K.W (ν k)) a h) =
    LinearMap.lTensor D (dw (W := K₀.W k) a).toLinearMap (Ta k h)) → (∀ l k' k (h₀ : K₀.le l k' k), Close ((RingHom.ker π).map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol (K₀.W k'))) ((Ta k').toRingHom.comp (Charts.sh (hν l k' k h₀))) (((Algebra.TensorProduct.map (AlgHom.id ℂ D) (Hol.comap (F₀.shift l) (F₀.shift_analytic l (K₀.base k')) (K₀.maps h₀))).comp (Ta k)).toRingHom)) → ∀ (φ₀ : X₀ ⟶ X), (∀ k, spMap ((Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W k))).comp π) (AlgHom.id ℂ (Hol (K₀.W k))) (fun _ _ ↦ Commute.all _ _)).comp (Ta k)).toRingHom ≫ r.x (ν k) = r₀.x k ≫ φ₀) → ∀ (j : B →+* D₀) (n : IsMor (dp0 B) s κ s' j φ₀), (∀ b, io (j b) = τV (σ b)) → ∀ (c : FirstDeRham s) (per : Λ →+ Hol F.V) (q : Λ →+ D), (∀ l, q l = τV (per l)) → r.coef.pull1 c = K.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (n.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ I _ F K B _ X s σ r ν hν Ta τV hc hd hcl φ₀ hpt
    j n hj c per q hq hper
  let β := coef π hπ K ν Ta τV hc hν hd hcl
  let θ : (r.coef.comp β).G ⟶ (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { RingHom.id (T.ten D) with commutes' := fun b ↦ congrArg (algebraMap D (T.ten D)) (hj b).symm }
          φ₀ := Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl
          comm := fun _ ↦ rfl
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat _ (T.tenδ π) (RingHom.id (T.ten D)) fun _ h ↦ h
          pt := by
            have e : (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl).comp
                ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) =
                ((Ideal.Quotient.mk T.J).comp T.ρ).comp ((Algebra.TensorProduct.lift
                  ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π) (AlgHom.id ℂ (Hol (K₀.W T.k)))
                  (fun _ _ ↦ Commute.all _ _)).comp (Ta T.k)).toRingHom := by
              have e' : ∀ x : D ⊗[ℂ] Hol (K₀.W T.k), T.red π (Algebra.TensorProduct.map (AlgHom.id ℂ D) T.ρc x) =
                  T.ρc (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol (K₀.W T.k))).comp π)
                    (AlgHom.id ℂ (Hol (K₀.W T.k))) (fun _ _ ↦ Commute.all _ _) x) := fun x ↦ by
                induction x using TensorProduct.induction_on with
                | zero => simp only [map_zero]
                | add x y hx hy => simp only [map_add (f := _), hx, hy]
                | tmul d c =>
                  rw [Algebra.TensorProduct.lift_tmul, map_mul]
                  exact congrArg (· * T.ρc c) (T.ρc.commutes (π d)).symm
              exact RingHom.ext fun h ↦ congrArg (Ideal.Quotient.mk T.J) (e' (Ta T.k h))
            change spMap (Ideal.quotientMap T.J (T.red π : T.ten D →+* T.C) le_rfl) ≫
              spMap ((Ideal.Quotient.mk (T.tenJ π)).comp (obj π hπ K ν Ta τV hc T).ρ) ≫ r.x (ν T.k) =
              (spMap ((Ideal.Quotient.mk T.J).comp T.ρ) ≫ r₀.x T.k) ≫ φ₀
            rw [Category.assoc, ← hpt]
            exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r.x (ν T.k)) ((Cris.spMap_comp _ _).symm.trans
              ((congrArg spMap e).trans (Cris.spMap_comp _ _)))).trans (Category.assoc _ _ _)) }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have h1 := (r.coef.comp β).pullCohomologyOne_eq_of_natTrans (n.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)) θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp, CoefMap.pullCohomologyOne_comp, hper] at h1
  refine h1.symm.trans (congrArg (GlobalTheory.CatCoh.H1.mk _) (Subtype.ext ?_))
  funext T T' f
  change algebraMap D (T'.ten D) (τV (per f.deg)) = algebraMap D (T'.ten D) (q f.deg)
  rw [hq]

end GlobalTheory.AnPer.TenFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenContractTmul
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.AnPer

open GlobalTheory.CatCoh

attribute [local instance] Charts.Obj.cAlg

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {D : Type} [CommRing D] [Algebra ℂ D]

def Charts.Obj.tenContract (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) : T.ten D →ₗ[ℂ] T.C :=
  (TensorProduct.lid ℂ T.C).toLinearMap ∘ₗ LinearMap.rTensor T.C ℓ

theorem Charts.Obj.tenContract_tmul (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) (d : D) (c : T.C) :
    T.tenContract ℓ (d ⊗ₜ c) = ℓ d • c := rfl

theorem Charts.Hom.tenContract_ten (ℓ : D →ₗ[ℂ] ℂ) {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.tenContract ℓ (Charts.Hom.ten D f x) = f.φ (T.tenContract ℓ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    rw [Charts.Hom.ten_tmul, Charts.Obj.tenContract_tmul, Charts.Obj.tenContract_tmul]
    exact (map_smul (Charts.Hom.φc f) (ℓ d) c).symm

theorem Charts.tenZ_eq_zero (K : Charts F) (hK : K.Rich) (hz : ∃ z, z ∈ F.V) {D : Type} [CommRing D] [Algebra ℂ D]
    (p : Λ →+ D) (h : H1.mk _ (K.tenZ p) = 0) : p = 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨G, hG⟩ := H1.mk_eq_zero.1 h
  refine AddMonoidHom.ext fun l ↦ (Module.forall_dual_apply_eq_zero_iff ℂ (p l)).1 fun ℓ ↦ ?_
  let q : Λ →+ Hol F.V := ((algebraMap ℂ (Hol F.V)).toAddMonoidHom.comp ℓ.toAddMonoidHom).comp p
  have h0 : K.perZ 0 = 0 := Subtype.ext (by
    funext T T' f
    exact map_zero (algebraMap (Hol F.V) T'.C))
  have hq : K.perCl q = K.perCl 0 := by
    unfold Charts.perCl
    rw [h0, map_zero]
    refine H1.mk_eq_zero.2 ⟨fun T ↦ T.tenContract ℓ (G T), ?_⟩
    funext T T' f
    have e : G T' - Charts.Hom.ten D f (G T) = (p f.deg ⊗ₜ[ℂ] (1 : T'.C) : T'.ten D) :=
      congrFun (congrFun (congrFun hG T) T') f
    have e' := congrArg (T'.tenContract ℓ) e
    rw [map_sub, Charts.Hom.tenContract_ten, Charts.Obj.tenContract_tmul, ← Algebra.algebraMap_eq_smul_one] at e'
    exact e'
  have h1 : algebraMap ℂ (Hol F.V) (ℓ (p l)) = 0 := DFunLike.congr_fun (GlobalTheory.T.periodClass_injective_of_rich_charts K hK q 0 hq) l
  have h2 := congrArg (Hol.ev z hz) h1
  rwa [AlgHom.commutes, map_zero] at h2

end GlobalTheory.AnPer
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.TaylorCore

open GlobalTheory.PeriodFamily GlobalTheory.CatCoh

theorem isNilpotent_of_isNilDP {D : Type} [CommRing D] {J : Ideal D} {κ : DividedPowers J} (h : IsNilDP κ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ (n : ℕ) (l : List D), (∀ x ∈ l, x ∈ J) → N ≤ l.length + n → ∀ y ∈ J ^ n, l.prod * y = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl hn y _
      have := hN (l.map fun x => (1, x)) (by simpa using hl) (by simpa [Function.comp_def] using hn)
      rw [List.map_map, List.map_congr_left (f := (fun p : ℕ × D ↦ κ.dpow p.1 p.2) ∘ fun x ↦ (1, x)) (g := id)
        fun x hx => κ.dpow_one (hl x hx), List.map_id] at this
      rw [this, zero_mul]
    | succ n ih =>
      intro l hl hn y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => by rw [mul_add, ha, hb, add_zero]
      have := ih (a :: l) (by simpa [ha] using hl) (by simp; omega) b hb
      rw [List.prod_cons] at this
      linear_combination this
  exact ⟨N, eq_bot_iff.2 fun y hy => by simpa using key N [] (by simp) (by simp) y hy⟩

def tayHom {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) : Hol V →+* D where
  toFun f := PeriodFamily.taylor N t f.fn
  map_one' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 1) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_one]),
      (taylor_formal_properties N t).2.2.1, map_one]
  map_zero' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 0) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_zero]),
      (taylor_formal_properties N t).2.2.1, map_zero]
  map_mul' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z * f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_mul _ _ hz),
      taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic _ h0) (f'.analytic _ h0)]
  map_add' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z + f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_add _ _ hz),
      (taylor_formal_properties N t).1 _ _ (f.analytic _ h0) (f'.analytic _ h0)]

theorem ev_red {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {D : Type} [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (p : E) (hp : p ∈ W) (x : D ⊗[ℂ] Hol W) :
    Hol.ev p hp (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol W)).comp π) (AlgHom.id ℂ (Hol W))
      (fun _ _ ↦ Commute.all _ _) x) =
    π (Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem main : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B _ X X₀ s s₀ σ e e₀ hX hX₀ h0 hV₀ hτ φ₀ hφ₀ D _ _ π κ hκ hπ N t ht htN j hj s' hs' n φ hφ k c per hper
    m d cs p ps hps hcs hdec l
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  obtain ⟨D', _, _, io, π', nn, hio, hpio, hnil, hn0, hn2, hnt⟩ := SquareZeroSum.exists_sum_sq_zero N D πa t
    (isNilpotent_of_isNilDP hκ) ht htN
  obtain ⟨M, hM⟩ := id hnil
  have hJ : ∀ s : Fin (N + M + 1) → D', (∀ a, s a ∈ RingHom.ker π') → ∏ a, s a = 0 := fun s hs => by
    have h1 : ∏ a, s a ∈ ∏ _a : Fin (N + M + 1), RingHom.ker π' := Ideal.prod_mem_prod fun a _ => hs a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Ideal.pow_le_pow_right (show M ≤ N + M + 1 by omega) h1
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have ht0 : ∀ i, π' (io (t i)) = 0 := fun i => (hpio _).trans (ht i)
  have ht' : ∀ s : Fin (N + M + 1) → I, ∏ a, io (t (s a)) = 0 := fun s => hJ _ fun a => ht0 _
  have hT : ∀ f, PeriodFamily.taylor (N + M) (fun i => io (t i)) f = io (PeriodFamily.taylor N t f) := fun f => by
    rw [← (taylor_formal_properties (N + M) t).2.2.2.2.1 D' io f, taylor_eq_of_le N t htN _ (Nat.le_add_right _ _)]
  have hred : ∀ f, π' (PeriodFamily.taylor (N + M) (fun i => io (t i)) f) = f 0 := fun f => by
    have h1 : PeriodFamily.taylor (N + M) (fun i => io (t i)) f - algebraMap ℂ D' (f 0) ∈ RingHom.ker π' :=
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht0 i)) ((taylor_formal_properties (N + M) _).2.2.2.2.2 f)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes] at h1
    exact h1
  obtain ⟨K₀, K, ν, hrich, hK₀, hK, hW, hν⟩ := ChartPair.exists_pair e₀ e (fun _ => 0) analyticOnNhd_const (fun _ _ => h0)
    LinearMap.id (AddMonoidHom.id Λ) fun l z _ => (hτ l z).symm
  obtain ⟨r₀, hr₀, -⟩ := exists_real_isFor e₀ hX₀ K₀ hK₀
  obtain ⟨r, hr, -⟩ := exists_real_isFor e hX K hK
  choose Ta hTa hTd using fun k => TaylorHom.exists_taylor_algHom (N + M) (fun i => io (t i)) ht' (K.W (ν k)) (K₀.W k) (hW k)
  let τV : Hol F.V →+* D' := tayHom (N + M) (fun i => io (t i)) ht' h0
  have hfam := TenFam.main π' r₀ rfl κ hs' (io : D →+* D') hpio hnil K r ν hν Ta τV
    (fun k f => tensor_hol_ext_of_values _ _ _ _ fun q hq => by
      rw [hTa k _ q hq, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      refine (taylor_formal_properties _ _).2.2.2.1 _ _ ?_
      have hc : Continuous fun z : I → ℂ => ((z, q.2) : Tot I g) := by fun_prop
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((K.W (ν k)).isOpen.mem_nhds (hW k q hq))] with z hz
      exact K.fn_cst _ f hz)
    hTd (fun l k' k h₀ => close_paramTaylor_shift F F₀ h0 hτ _ (N + M) hJ _ N nn hn0 hn2 hnt K K₀ l _ _ k k' (hν l k' k h₀) h₀
      (hW k') (Ta k) (Ta k') (hTa k) (hTa k')) φ₀
    (fun k => point_hol_ext_of_isSeparated _ hX _ _ fun q hq => by
      rw [← Category.assoc, ← Category.assoc, hr₀ k q hq, hφ₀ q (K₀.base k q hq), ← hr (ν k) (0, q.2) (hW k q hq),
        ← Cris.spMap_comp]
      refine congrArg (fun ψ => spMap ψ ≫ r.x (ν k)) (RingHom.ext fun h => ?_)
      refine (ev_red π' q hq (Ta k h)).trans ?_
      rw [hTa k h q hq, hred]
      exact (Hol.ev_apply _ _ _).symm)
    j n (fun b => (congrArg io (hj b)).trans (hT _).symm) c per (τV.toAddMonoidHom.comp per) (fun _ => rfl) (hper K r hr)
  obtain ⟨z₀, hz₀⟩ := hV₀
  let q : Fin m → Λ →+ D' := fun i => ((algebraMap ℂ D').comp (Hol.ev z₀ hz₀).toRingHom).toAddMonoidHom.comp (ps i)
  have hq : ∀ i l, q i l = algebraMap ℂ D' (p i l) := fun i l =>
    congrArg (algebraMap ℂ D') ((congrArg (Hol.ev z₀ hz₀) (hps i l)).trans ((Hol.ev z₀ hz₀).commutes _))
  have hfib := fun i => TenFib.ten_fib π' r₀ rfl κ hs' (io : D →+* D') hpio hnil (algebraMap ℂ D) φ hφ k io.commutes (cs i) (p i)
    (ps i) (q i) (hps i) (hq i) (hcs i K₀ r₀ hr₀)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum] at hfam
  simp only [LinearMap.map_smulₛₗ, hfib] at hfam
  have hz : K₀.tenZ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) =
      ∑ i, io (d i) • K₀.tenZ (q i) - K₀.tenZ (τV.toAddMonoidHom.comp per) := by
    let Z : (Λ →+ D') →ₗ[D'] Z1 (K₀.Ten D') :=
      { toFun := K₀.tenZ
        map_add' := fun a b => Subtype.ext (by funext T T' f; exact map_add (algebraMap D' (T'.ten D')) _ _)
        map_smul' := fun a b => Subtype.ext (by
          funext T T' f
          exact (map_mul (algebraMap D' (T'.ten D')) _ _).trans (Algebra.smul_def _ _).symm) }
    change Z _ = ∑ i, io (d i) • Z _ - Z _
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul]
  have := Charts.tenZ_eq_zero K₀ hrich ⟨z₀, hz₀⟩ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sub, ← hfam, map_sum]
    simp only [map_smul]
    exact sub_self _)
  have h1 := DFunLike.congr_fun (sub_eq_zero.1 this) l
  refine hio ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hT, map_sum]
  refine Eq.trans ?_ h1
  change _ = (AddMonoidHom.eval l) (∑ i, io (d i) • q i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    change io (d i * algebraMap ℂ D (p i l)) = (io (d i) • q i) l
    rw [map_mul, io.commutes, AddMonoidHom.smul_apply, hq, smul_eq_mul]

end GlobalTheory.AnPer.TaylorCore
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnPer.TaylorClause

theorem isSep {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] (h : IsAbelianScheme A) : A.left.IsSeparated := by
  have : IsProper A.hom := h.proper
  rw [Scheme.isSeparated_iff, ← Limits.terminal.comp_from A.hom]
  infer_instance

theorem of_core0 (core : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn) :
    PTaylor := by
  intro I _ _ g B _ _ 𝒜 _ hA hg y₀ A₀ _ φ₀ h₀ L₀ u₀ F σ e h0 hy hE hτ P₀ hP D _ _ π κ hκ hπ N t ht hN j hj
    A' _ φ' h' m' i h hi k x d hd c per hper
  obtain ⟨hA₀, hg₀⟩ := GlobalTheory.AbBaseChange.isAbelianScheme_and_relDim_of_isGrpPullback _ 𝒜 A₀ φ₀ g h₀ hA hg
  have hsp := (GlobalTheory.T.primitiveCrystalline_baseChange_nilpotent_thickening A₀ g hA₀ hg₀ D π κ hκ hπ k).2
  have hm : (liftMor κ h).pull (m'.pull c) ∈ Submodule.span D (Set.range k.pull) := by rw [hsp]; trivial
  obtain ⟨m, dd, v, hv⟩ := Submodule.mem_span_set'.1 hm
  choose cs hcs using fun a ↦ (v a).2
  have n : IsMor (dp0 B) (𝒜.hom ≫ 𝟙 _) κ (A₀.hom ≫ spMap π) (j : B →+* D) φ₀ := by
    have := m'.isMor.comp (liftMor κ h).isMor
    rwa [RingHom.id_comp, hi] at this
  have hn : n.pull1 c.1 = ∑ a, dd a • k.isMor.pull1 (cs a).1 := by
    rw [← IsMor.pullback1_comp m'.isMor (liftMor κ h).isMor n (fun _ ↦ rfl) hi c.1]
    have := congrArg Subtype.val hv
    rw [Submodule.coe_sum] at this
    refine this.symm.trans (Finset.sum_congr rfl fun a _ ↦ ?_)
    rw [← hcs a]
    rfl
  have key := core (F₀ := fibFam u₀) e (fibUnif u₀) (isSep 𝒜 hA) (isSep A₀ hA₀) h0 ⟨fun a ↦ a.elim, trivial⟩
    (fun l _ ↦ (hτ l).symm) φ₀ (fun p _ ↦ (hE p.2).symm) D π κ hκ hπ N t ht hN (j : B →+* D) hj
    (A₀.hom ≫ spMap π) (by rw [Category.comp_id]) n (Over.Hom.left (𝟙 A₀)) rfl k.isMor c.1 per hper m dd
    (fun a ↦ (cs a).1) (fun a l ↦ P₀ l (cs a)) _ (fun _ _ ↦ rfl) (fun a ↦ hP (cs a)) hn x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← key, crysToDR_apply, ← hv, map_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [map_smul, ← hcs a, hd, smul_eq_mul]

theorem pTaylor0 : PTaylor := of_core0 GlobalTheory.AnPer.TaylorCore.main

end GlobalTheory.AnPer.TaylorClause
end
end

open GlobalTheory.AnPer

namespace GlobalTheory.PeriodFamily

theorem gaussManinPeriods_holds : GlobalTheory.Published.GaussManinPeriods :=
  gaussManinPeriods_of_span_taylor GlobalTheory.T.periods_span_deRhamHomology_rank_two_g
    GlobalTheory.AnPer.TaylorClause.pTaylor0

end GlobalTheory.PeriodFamily
end

theorem GlobalTheory.PeriodFamily.periodComparison_holds : GlobalTheory.Published.PeriodComparison :=
  GlobalTheory.PeriodFamily.periodComparison_of_gaussManinPeriods GlobalTheory.PeriodFamily.gaussManinPeriods_holds
