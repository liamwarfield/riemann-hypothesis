module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltration
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBanachModelTensorAcris

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFil
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFil
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.ExpImage.PolyTaylor

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {R : Type*} [CommRing R]

theorem eval₂_mem_zero (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 0) (q : Polynomial R) : q.eval₂ φ τ ∈ FilB P 0 := by
  rw [Polynomial.eval₂_eq_sum_range]
  exact Submodule.sum_mem _ fun k _ => FilB_zero_mul (hφ _) (by simpa using FilB_pow hτ k)

theorem trunc_mul_sub_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (f g : PowerSeries R) :
    (f.trunc m).eval₂ φ τ * (g.trunc m).eval₂ φ τ - ((f * g).trunc m).eval₂ φ τ ∈
      FilB P (m : ℤ) := by
  have hd : Polynomial.X ^ m ∣ f.trunc m * g.trunc m - (f * g).trunc m := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub, PowerSeries.coeff_trunc, if_pos hd,
      PowerSeries.coeff_mul_eq_coeff_trunc_mul_trunc f g hd, ← Polynomial.coe_mul,
      Polynomial.coeff_coe, sub_self]
  obtain ⟨q, hq⟩ := hd
  rw [← Polynomial.eval₂_mul, ← Polynomial.eval₂_sub, hq, Polynomial.eval₂_mul,
    Polynomial.eval₂_X_pow, mul_comm]
  exact FilB_zero_mul (eval₂_mem_zero φ hφ (FilB_anti zero_le_one hτ) q)
    (by simpa using FilB_pow hτ m)

theorem eval₂_sub_trunc_mem (φ : R →+* P.R.BdR) (hφ : ∀ x, φ x ∈ FilB P 0) {τ : P.R.BdR}
    (hτ : τ ∈ FilB P 1) (m : ℕ) (E : PowerSeries R) {v : P.R.BdR} (hv : v ∈ FilB P 0)
    (hE : v - (E.trunc m).eval₂ φ τ ∈ FilB P (m : ℤ)) (p : Polynomial R) :
    p.eval₂ φ v - ((Polynomial.aeval E p).trunc m).eval₂ φ τ ∈ FilB P (m : ℤ) := by
  have hτ0 := FilB_anti zero_le_one hτ
  induction p using Polynomial.induction_on with
  | C a =>
    rcases m with _ | m
    · exact sub_mem (eval₂_mem_zero φ hφ hv _) (eval₂_mem_zero φ hφ hτ0 _)
    · rw [Polynomial.aeval_C, ← PowerSeries.C_eq_algebraMap, PowerSeries.trunc_C]
      simp
  | add p q hp hq =>
    have := add_mem hp hq
    rw [map_add (f := _), map_add (f := _), Polynomial.eval₂_add, Polynomial.eval₂_add]
    convert this using 1
    ring
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Polynomial.eval₂_mul,
      Polynomial.eval₂_X]
    have h1 := FilB_zero_mul hv h
    have h2 := FilB_zero_mul (eval₂_mem_zero φ hφ hτ0
      ((Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)).trunc m)) hE
    have h3 := trunc_mul_sub_mem φ hφ hτ m
      (Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n)) E
    have := add_mem (add_mem h1 h2) h3
    convert this using 1
    ring

theorem poly_taylor : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  intro l _ P AI T LL s ζ ι hζ p m
  have hφ : ∀ x, (ι : ↥LL.1 →+* P.R.BdR) x ∈ FilB P 0 := EmbFil.emb_mem_fil_zero l P AI T LL ι
  have hτ : (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB ∈ FilB P 1 := by
    rw [Algebra.smul_def]
    exact qB_mul_mem _ tD_mem
  have hv : P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) ∈ FilB P 0 := io_mem AI _
  have key := eval₂_sub_trunc_mem (ι : ↥LL.1 →+* P.R.BdR) hφ hτ m
    (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) hv ?_ p
  · rw [PowerSeries.eval₂_trunc_eq_sum_range] at key
    exact key
  rcases m with _ | m
  · exact sub_mem hv (eval₂_mem_zero _ hφ (FilB_anti zero_le_one hτ) _)
  have h := GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI T s 1 (m + 1)
  rw [map_sub (PowerSeries.trunc (m + 1)), PowerSeries.trunc_one, Polynomial.eval₂_sub,
    Polynomial.eval₂_one, PowerSeries.eval₂_trunc_eq_sum_range, ← io_apply, map_sub, map_one,
    sub_sub_sub_cancel_right]
  rw [pow_one, pow_one, Finset.mul_sum] at h
  suffices hs : ∑ k ∈ Finset.range (m + 1), (ι : ↥LL.1 →+* P.R.BdR)
      (PowerSeries.coeff k (PowerSeries.C ζ * PowerSeries.exp ↥LL.1)) *
        ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k = ∑ k ∈ Finset.range (m + 1), oB P (P.ζQ s) *
          (qB P ((((1 : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ k / (k.factorial : ℚ_[l])) * tD P ^ k) by
    rw [hs]
    exact h
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ι (algebraMap ℚ ↥LL.1 (1 / (k.factorial : ℚ))) = qB P (1 / (k.factorial : ℚ_[l])) := by
    rw [← ι.commutes]
    congr 1
    simp
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_exp, map_mul, RingHom.coe_coe, hζ, hk,
    Algebra.smul_def, mul_pow, ← map_pow, mul_assoc, ← mul_assoc (qB P _), ← map_mul]
  congr 3
  simp [div_eq_mul_inv, mul_comm]

end GlobalTheory.ExpImage.PolyTaylor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialTeichmullerRootTaylorModFilStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_teichmullerRoot_taylor_modFil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (LL : FinExt l) (s : ℕ) (ζ : ↥LL.1) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), ι ζ = algebraMap (Om l) P.R.BdR (P.ζQ s) → ∀ (p : Polynomial ↥LL.1) (m : ℕ), Polynomial.eval₂ (ι : ↥LL.1 →+* P.R.BdR) (P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1))) p - ∑ k ∈ Finset.range m, ι (PowerSeries.coeff k (Polynomial.aeval (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) p)) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k ∈ GlobalTheory.ExpImage.FilB P (m : ℤ) := by
  first | exact @GlobalTheory.ExpImage.PolyTaylor.poly_taylor | exact GlobalTheory.ExpImage.PolyTaylor.poly_taylor | (intros; apply GlobalTheory.ExpImage.PolyTaylor.poly_taylor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstant
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstant
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EvalIdem

theorem ringHom_eq_of_unique {O A S : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing S]
    (Q : A → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : A →ₐ[O] S), (∀ a, Q a → f a = f' a) → f = f')
    (F F' : A →+* S) (h0 : ∀ o, F (algebraMap O A o) = F' (algebraMap O A o))
    (h1 : ∀ a, Q a → F a = F' a) (a : A) : F a = F' a := by
  let _ : Algebra O S := (F.comp (algebraMap O A)).toAlgebra
  have := h S ⟨F, fun _ => rfl⟩ ⟨F', fun o => (h0 o).symm⟩ h1
  exact DFunLike.congr_fun this a

theorem io_const {O T : Type} [CommRing O] [CommRing T] [Algebra O T] {n : ℕ} (f : LetA O n →ₐ[O] T) (x : O) :
    f (fun j => PowerSeries.C (algebraMap O (ZMod n → O) x j)) = algebraMap O T x := f.commutes x

theorem const_eq {O T S : Type} [CommRing O] [CommRing T] [Algebra O T] [CommRing S] {n : ℕ}
    (Q : (ZMod n → O) → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : (ZMod n → O) →ₐ[O] S),
      (∀ a, Q a → f a = f' a) → f = f')
    (f : LetA O n →ₐ[O] T) (G : T →+* S) (e : O →+* S) (i : ZMod n)
    (h0 : ∀ x, G (algebraMap O T x) = e x)
    (h1 : ∀ a, Q a → G (f (fun j => PowerSeries.C (a j))) = e (a i)) (a : ZMod n → O) :
    G (f (fun j => PowerSeries.C (a j))) = e (a i) :=
  ringHom_eq_of_unique Q h
    (G.comp (f.toRingHom.comp (RingHom.pi fun j =>
      (PowerSeries.C : O →+* PowerSeries O).comp (Pi.evalRingHom _ j))))
    (e.comp (Pi.evalRingHom _ i)) (fun x => (congrArg G (io_const f x)).trans (h0 x)) h1 a

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l}

theorem component_tmul {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) (w : Ainf l) :
    Algebra.TensorProduct.productMap ι P.ιB (β (x ⊗ₜ[ℤ_[l]] w)) = ι (x : ↥LL.1) * P.ιB (AI.ιA w) := by
  rw [hβ, Algebra.TensorProduct.productMap_apply_tmul]

theorem component_algebraMap {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) :
    Algebra.TensorProduct.productMap ι P.ιB (β (algebraMap ↥(OL LL) (RA LL) x)) = ι (x : ↥LL.1) := by
  have h1 : algebraMap ↥(OL LL) (RA LL) x = x ⊗ₜ[ℤ_[l]] (1 : Ainf l) := rfl
  rw [h1, component_tmul hβ, map_one, map_one, mul_one]

theorem component_teich {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) {K : FinExt l} (c : ↥(K0 K)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m)
    (hc : (c : Om l) ^ m = 1) (xb : OCb l) (hxb : IsTiltOf (c : Om l) m xb) :
    Algebra.TensorProduct.productMap ι P.ιB
      (β ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb)) = algebraMap ↥(K0 K) P.R.BdR c := by
  rw [component_tmul hβ, AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb, GlobalTheory.LocIota.ιB_algebraMap_Kur,
    OneMemClass.coe_one, map_one, one_mul]
  rfl


set_option maxHeartbeats 800000 in
theorem component_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  intro l _ P AI T K s LL hG Γ R I hI β hβ i ι hι o
  obtain ⟨-, -, hu⟩ := GlobalTheory.T.unramifiedIntegers_tensor_eq_letterwise_product_Ainf l P K s LL hG Γ.emb Γ.emb_bij
  refine const_eq
    (fun a => ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
      ∀ j, ((a j : ↥(OL LL)) : ↥LL.1) = Γ.emb j c)
    (fun S _ _ f f' h => hu S f f' fun c m hm hl hc a ha => h a ⟨c, m, hm, hl, hc, ha⟩) I.io
    ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp β)
    (ι.toRingHom.comp (algebraMap ↥(OL LL) ↥LL.1)) i (component_algebraMap hβ ι) ?_ o
  rintro a ⟨c, m, hm, hl, hc, ha⟩
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have h1 := component_teich hβ ι c m hm hl hc xb hxb
  rw [← hI c m hm hl hc xb hxb a ha, ← hι, ← ha] at h1
  exact h1

end GlobalTheory.EvalIdem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstantStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  first | exact @GlobalTheory.EvalIdem.component_const | exact GlobalTheory.EvalIdem.component_const | (intros; apply GlobalTheory.EvalIdem.component_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGalois
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGalois
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.IoComm

variable {l : ℕ} [Fact l.Prime]

theorem transfer {Z O A W S : Type} [CommRing Z] [CommRing O] [CommRing A] [CommRing W] [CommRing S]
    [Algebra Z O] [Algebra Z A] [Algebra Z W] (j : A →ₐ[Z] W)
    (hj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id O O) j))
    (ψ : A →ₐ[Z] A) (Ψ : W →ₐ[Z] W) (h : ∀ w, Ψ (j w) = j (ψ w)) (f f' : O ⊗[Z] A →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[Z] w) = f (o ⊗ₜ[Z] ψ w)) (x y : O ⊗[Z] A)
    (hxy : Algebra.TensorProduct.map (AlgHom.id O O) j y =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j x)) :
    f y = f' x := by
  let Φ : O ⊗[Z] A →ₐ[O] O ⊗[Z] A := Algebra.TensorProduct.map (AlgHom.id _ _) ψ
  have h1 : ∀ z : O ⊗[Z] A, Algebra.TensorProduct.map (AlgHom.id O O) j (Φ z) =
      Algebra.TensorProduct.map (AlgHom.id O O) Ψ (Algebra.TensorProduct.map (AlgHom.id O O) j z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, h]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : ∀ z : O ⊗[Z] A, f (Φ z) = f' z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul o w =>
      rw [hf]
      simp only [Φ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h3 : y = Φ x := hj (hxy.trans (h1 x).symm)
  rw [h3, h2]

def frobA (l : ℕ) [Fact l.Prime] : Ainf l →ₐ[ℤ_[l]] Ainf l where
  toRingHom := WittVector.map (frobenius (OCb l) l)
  commutes' := fun x => map_zlW l _ x

theorem frobA_apply (w : Ainf l) : frobA l w = WittVector.frobenius w := by
  rw [WittVector.frobenius_eq_map_frobenius]
  rfl

theorem frobW_inclWA (w : Ainf l) : frobW l (inclWA l w) = inclWA l (frobA l w) := by
  ext n
  change frobenius (Cb l) l (algebraMap (OCb l) (Cb l) (w.coeff n)) =
    algebraMap (OCb l) (Cb l) (frobenius (OCb l) l (w.coeff n))
  rw [frobenius_def, frobenius_def, map_pow]

theorem act_inclWA {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (w : Ainf l) :
    (AI.actWCbHom g).toAlgHom (inclWA l w) = inclWA l ((AI.actWHom g).toAlgHom w) := by
  ext n
  exact autCb_alg l (AI.actT g) (w.coeff n)

section

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l} {Γ : GamS P K s LL}
  {R : WSer Γ} (I : IoS AI R)

theorem incl_io_φ (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letφ R.φ₀ a)) = φRW LL (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.φE_ext a).symm)).trans
    ((I.ioE_φ _).trans (congrArg (φRW LL) (I.ioE_ext a)))

theorem incl_io_γ (g : ↥(GK K)) (a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) :
    inclR LL (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = AI.gRW LL (g : GQ l) (inclR LL (I.io a)) :=
  ((I.ioE_ext _).symm.trans (congrArg I.ioE (R.γE_ext _ a).symm)).trans
    ((I.ioE_γ g _).trans (congrArg (AI.gRW LL (g : GQ l)) (I.ioE_ext a)))

end

theorem transfer_φ (LL : FinExt l) {S : Type} [CommRing S] (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) (x y : RA LL)
    (hxy : inclR LL y = φRW LL (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (frobA l) (frobW l) frobW_inclWA f f'
    (fun o w => by rw [frobA_apply, hf]) x y hxy

theorem transfer_γ {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (LL : FinExt l) {S : Type} [CommRing S]
    (f f' : RA LL →+* S)
    (hf : ∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW g w)) (x y : RA LL)
    (hxy : inclR LL y = AI.gRW LL g (inclR LL x)) : f y = f' x :=
  transfer (inclWA l) (GlobalTheory.HWL.TensorWitt.main l LL).2.2.1 (AI.actWHom g).toAlgHom
    (AI.actWCbHom g).toAlgHom (act_inclWA AI g) f f' (fun o w => hf o w) x y hxy

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  intro l _ P AI K s LL Γ R I S _ f f'
  exact ⟨fun hf a => transfer_φ LL f f' hf _ _ (incl_io_φ I a),
    fun g hf a => transfer_γ AI (g : GQ l) LL f f' hf _ _ (incl_io_γ I g a)⟩

end GlobalTheory.HWL.IoComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionLayerIoCommutesFrobeniusGaloisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ) (LL : FinExt l) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R) (S : Type) [CommRing S] (f f' : RA LL →+* S), ((∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] WittVector.frobenius w)) → ∀ a, f (I.io (letφ R.φ₀ a)) = f' (I.io a)) ∧ ∀ g : ↥(GK K), (∀ o w, f' (o ⊗ₜ[ℤ_[l]] w) = f (o ⊗ₜ[ℤ_[l]] AI.actW (g : GQ l) w)) → ∀ a, f (I.io (letγ (R.γ₀ (Γ.resΓ g)) a)) = f' (I.io a) := by
  first | exact @GlobalTheory.HWL.IoComm.main | exact GlobalTheory.HWL.IoComm.main | (intros; apply GlobalTheory.HWL.IoComm.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNorm
noncomputable section

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter Finset GlobalTheory.HWL.Disc

variable {K : Type} [NormedField K] {N : Type} [NormedCommRing N]

def Small (ν : N) : Prop := ∃ C r : ℝ, 0 < r ∧ r < 1 ∧ ∀ k : ℕ, ‖ν ^ k‖ ≤ C * r ^ k

def Bdd (c : K →+* N) : Prop := ∃ C : ℝ, ∀ x, ‖c x‖ ≤ C * ‖x‖

def ev (c : K →+* N) (ν : N) (a : K⟦X⟧) : N := ∑' k : ℕ, c (coeff k a) * ν ^ k

variable {c : K →+* N} {ν : N}

theorem Bdd.continuous (hc : Bdd c) : Continuous c := by
  obtain ⟨C, h⟩ := hc
  exact AddMonoidHomClass.continuous_of_bound c C h

theorem exists_bound (hc : Bdd c) (hν : Small ν) :
    ∃ C r : ℝ, 0 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ (x : K) (k : ℕ), ‖c x * ν ^ k‖ ≤ C * (‖x‖ * r ^ k) := by
  obtain ⟨C, h⟩ := hc
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine ⟨|C| * |D|, r, by positivity, h0, h1, fun x k => (norm_mul_le _ _).trans ?_⟩
  have e1 : ‖c x‖ ≤ |C| * ‖x‖ := (h x).trans (by gcongr; exact le_abs_self C)
  have e2 : ‖ν ^ k‖ ≤ |D| * r ^ k := (h2 k).trans (by gcongr; exact le_abs_self D)
  calc _ ≤ (|C| * ‖x‖) * (|D| * r ^ k) := by gcongr
    _ = _ := by ring

theorem summable_norm (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Summable fun k : ℕ => ‖c (coeff k a) * ν ^ k‖ := by
  obtain ⟨C, r, -, h0, h1, h⟩ := exists_bound hc hν
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => h _ k) ((ha r h0 h1).mul_left C)

theorem Small.tendsto (hν : Small ν) : Tendsto (fun k : ℕ => ν ^ k) atTop (nhds 0) := by
  obtain ⟨D, r, h0, h1, h2⟩ := hν
  refine squeeze_zero_norm h2 ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul D

theorem ev_C_mul (hc : Bdd c) (hν : Small ν) [CompleteSpace N] (x : K) {a : K⟦X⟧} (ha : SC a) :
    ev c ν (x • a) = c x * ev c ν a := by
  rw [ev, ev, ← (summable_norm hc hν ha).of_norm.tsum_mul_left]
  simp [mul_assoc]

theorem sum_range_eq (a : K⟦X⟧) (m : ℕ) :
    ∑ k ∈ range m, c (coeff k a) * ν ^ k = Polynomial.eval₂ c ν (trunc m a) := by
  rw [eval₂_trunc_eq_sum_range]

variable [CompleteSpace N]

theorem hasSum_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ν ^ k) (ev c ν a) :=
  (summable_norm hc hν ha).of_norm.hasSum

theorem tendsto_ev (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) :
    Tendsto (fun m : ℕ => Polynomial.eval₂ c ν (trunc m a)) atTop (nhds (ev c ν a)) := by
  simpa only [sum_range_eq] using (hasSum_ev hc hν ha).tendsto_sum_nat

theorem ev_add (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a + b) = ev c ν a + ev c ν b := by
  refine HasSum.tsum_eq ?_
  simpa only [map_add (f := _), add_mul] using (hasSum_ev hc hν ha).add (hasSum_ev hc hν hb)

theorem ev_mul (hc : Bdd c) (hν : Small ν) {a b : K⟦X⟧} (ha : SC a) (hb : SC b) :
    ev c ν (a * b) = ev c ν a * ev c ν b := by
  rw [ev, ev, ev, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm hc hν ha)
    (summable_norm hc hν hb)]
  refine tsum_congr fun k => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [coeff_mul, map_sum, sum_mul]
  refine sum_congr rfl fun p hp => ?_
  rw [← mem_antidiagonal.1 hp, map_mul, pow_add]
  ring

theorem ev_one : ev c ν 1 = 1 := by
  rw [ev, tsum_eq_single 0 fun k hk => by simp [coeff_one, hk]]
  simp

theorem sc_pow {a : K⟦X⟧} (ha : SC a) (k : ℕ) : SC (a ^ k) := by
  induction k with
  | zero => simpa using sc_coe (1 : Polynomial K)
  | succ k ih => rw [pow_succ]; exact ih.mul ha

theorem ev_pow (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (k : ℕ) :
    ev c ν (a ^ k) = ev c ν a ^ k := by
  induction k with
  | zero => simpa using ev_one
  | succ k ih => rw [pow_succ, pow_succ, ev_mul hc hν (sc_pow ha k) ha, ih]

theorem hasSum_map (hc : Bdd c) (hν : Small ν) {a : K⟦X⟧} (ha : SC a) (f : N →+* N) (hf : Continuous f)
    (hfc : ∀ x, f (c x) = c x) : HasSum (fun k : ℕ => c (coeff k a) * f ν ^ k) (f (ev c ν a)) := by
  have := (hasSum_ev hc hν ha).map f hf
  simpa only [Function.comp_def, map_mul, map_pow, hfc] using this

theorem ev_map {O : Type} [CommRing O] (j : O →+* K) (hν : Small ν) (hc : Bdd c) (f : O⟦X⟧ →+* N)
    (hC : ∀ o, f (C o) = c (j o)) (hX : f X = ν) (hf : ∀ a, ‖f a‖ ≤ 1) (a : O⟦X⟧) (ha : SC (map j a)) :
    ev c ν (map j a) = f a := by
  refine tendsto_nhds_unique (hasSum_ev hc hν ha).tendsto_sum_nat ?_
  have key : ∀ m : ℕ, ∑ k ∈ range m, c (coeff k (map j a)) * ν ^ k =
      f a - ν ^ m * f (mk fun i => coeff (i + m) a) := by
    intro m
    have e0 := congrArg f (eq_X_pow_mul_shift_add_trunc m a)
    rw [e0, map_add (f := _), map_mul, map_pow, hX, add_sub_cancel_left, trunc_apply, Polynomial.coe_def]
    have e : (mk (∑ k ∈ Ico 0 m, Polynomial.monomial k (coeff k a)).coeff : O⟦X⟧) =
        ∑ k ∈ range m, C (coeff k a) * X ^ k := by
      ext n
      simp [coeff_X_pow, Polynomial.coeff_monomial, Polynomial.finsetSum_coeff, Finsupp.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp only [map_mul, map_pow, hX, hC, coeff_map]
  simp only [key]
  conv => rhs; rw [← sub_zero (f a)]
  refine tendsto_const_nhds.sub (squeeze_zero_norm (a := fun m => ‖ν ^ m‖) (fun m => ?_) ?_)
  · exact (norm_mul_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) (hf _))
  · simpa using hν.tendsto.norm

theorem hasSum_subst [IsUltrametricDist K] (hc : Bdd c) (hν : Small ν) {y a : K⟦X⟧} (hy0 : constantCoeff y = 0)
    (hy : ∀ k, ‖coeff k y‖ ≤ 1) (ha : SC a) :
    HasSum (fun k : ℕ => c (coeff k a) * ev c ν y ^ k) (ev c ν (subst y a)) := by
  obtain ⟨C, r, hC, h0, h1, h⟩ := exists_bound hc hν
  have hy' : SC y := sc_of_le 0 fun k => by simpa using hy k
  have hp : ∀ k n, ‖coeff n (y ^ k)‖ ≤ 1 := fun k n => by
    simpa using norm_coeff_pow_le y n (r := 1) (R := 1) zero_le_one zero_le_one (fun i _ => by simpa using hy i) k n le_rfl
  have hz : ∀ k n, n < k → coeff n (y ^ k) = 0 := fun k n hn =>
    X_pow_dvd_iff.1 (pow_dvd_pow_of_dvd (X_dvd_iff.2 hy0) k) n hn
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ r = ρ * ρ :=
    ⟨√r, Real.sqrt_pos.2 h0, by rwa [Real.sqrt_lt' one_pos, one_pow], (Real.mul_self_sqrt h0.le).symm⟩
  let F : ℕ × ℕ → N := fun p => c (coeff p.1 a * coeff p.2 (y ^ p.1)) * ν ^ p.2
  have hF : Summable F := by
    refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => (C * (‖coeff p.1 a‖ * ρ ^ p.1)) * ρ ^ p.2)
      (Summable.mul_of_nonneg ((ha ρ hρ0 hρ1).mul_left C) (summable_geometric_of_lt_one hρ0.le hρ1)
        (fun _ => by positivity) fun _ => by positivity) fun p => ?_
    by_cases hlt : p.2 < p.1
    · simp only [F, hz _ _ hlt, mul_zero, map_zero, zero_mul, norm_zero]
      positivity
    · refine (h _ _).trans ?_
      have e : ρ ^ p.2 ≤ ρ ^ p.1 := pow_le_pow_of_le_one hρ0.le hρ1.le (not_lt.1 hlt)
      rw [norm_mul, hρ, mul_pow]
      calc _ ≤ C * (‖coeff p.1 a‖ * 1 * (ρ ^ p.1 * ρ ^ p.2)) := by gcongr; exact hp _ _
        _ = _ := by ring
  have h2 : HasSum (fun n : ℕ => c (coeff n (subst y a)) * ν ^ n) (∑' p, F p) := by
    refine HasSum.prod_fiberwise ((Equiv.prodComm ℕ ℕ).hasSum_iff.2 hF.hasSum) fun n => ?_
    have e : coeff n (subst y a) = ∑ k ∈ range (n + 1), coeff k a * coeff n (y ^ k) := by
      rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hy0), finsum_eq_sum_of_support_subset (s := range (n + 1))]
      · simp
      · intro k hk
        by_contra hk'
        apply hk
        simp only [coe_range, Set.mem_Iio, not_lt] at hk'
        simp [hz k n hk']
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, sum_mul]
    refine hasSum_sum_of_ne_finset_zero fun k hk => ?_
    simp only [mem_range, not_lt] at hk
    simp [F, hz k n hk]
  rw [show ev c ν (subst y a) = _ from h2.tsum_eq]
  refine HasSum.prod_fiberwise hF.hasSum fun k => ?_
  rw [← ev_pow hc hν hy']
  simpa only [F, map_mul, mul_assoc] using (hasSum_ev hc hν (sc_pow hy' k)).mul_left (c (coeff k a))

end GlobalTheory.HWL.BanachEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcris
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.HWL.BanachEval

open PowerSeries Filter GlobalTheory.HWL.Disc

section Letters

variable {O N : Type} [CommRing O] [CommRing N] {n : ℕ} [NeZero n] (f : LetA O n →+* N)

theorem sum_letE : ∑ i, f (letE i) = 1 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, ← map_one f]
  exact congrArg f (Finset.univ_sum_single (1 : LetA O n))

theorem sum_letE_mul (x y : ZMod n → N) :
    ∑ i, f (letE i) * (x i * y i) = (∑ i, f (letE i) * x i) * ∑ i, f (letE i) * y i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have : (letE i : LetA O n) * letE i = letE i := by
      ext1 j
      by_cases h : j = i <;> simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this]
  · intro j _ hj
    have : (letE i : LetA O n) * letE j = 0 := by
      ext1 k
      by_cases h : k = i
      · simp [letE, h, hj.symm]
      · simp [letE, h]
    rw [mul_mul_mul_comm, ← map_mul, this, map_zero, zero_mul]
  · simp

theorem sum_letE_const (a : LetA O n) : ∑ i, f (letE i) * f (fun _ => a i) = f a := by
  simp only [← map_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum]
  congr 1
  ext1 j
  simp [letE, Pi.single_apply]

omit [NeZero n] in
theorem letφ_letE (φ₀ : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letφ φ₀ (letE (i - 1)) = letE i := by
  ext1 j
  change φ₀ ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases h : j = i <;> simp [letE, h]

omit [NeZero n] in
theorem letγ_letE (g : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letγ g (letE i) = letE i := by
  ext1 j
  change g ((letE i : LetA O n) j) = _
  by_cases h : j = i <;> simp [letE, h]

end Letters

variable {l : ℕ} [Fact l.Prime]

theorem frob_root {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    WittVector.frobenius (WittVector.teichmuller l (AI.εroot (s + 1)) - 1) =
      WittVector.teichmuller l (AI.εroot s) - 1 := by
  rw [map_sub, map_one, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
    LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

theorem sc_map {LL : FinExt l} (a : (↥(OL LL))⟦X⟧) : SC (map (algebraMap ↥(OL LL) ↥LL.1) a) :=
  sc_of_le 0 fun k => by simpa using norm_integer_le_one (coeff k a)

theorem sc_log (LL : FinExt l) : SC (logS LL) := sc_lg (norm_natCast_inv_le LL)

theorem frob_injective {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (LL : FinExt l) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ_[l] ↥LL.1) P.φB) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := ↥LL.1) P.φB.toLinearMap
    (GlobalTheory.Per.TiedField.tied_field l P AI T).2.2.2.1

theorem crisFrobenius_periodT_eq_prime_smul (P : LocPrime l) (K : FinExt l) : P.φB P.tB = (l : ℚ_[l]) • P.tB := by
  have h := (P.PD K).t_φ
  rwa [P.PD_φ, P.period_datum_t_eq, P.PD_p] at h


set_option maxHeartbeats 1000000 in
theorem exists_eval : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  intro l _ P AI T K s LL hG Γ R I hW β hβ
  obtain ⟨N, _, _, c, b, κ, φ, γ, t, ⟨hκb, hφb, hκφ, hγb, hκγ, hκt⟩, hc, hb, hbo, hκc, ⟨hφ, hφc⟩, hγ, hs, hlog, hcl⟩ :=
    GlobalTheory.T.exists_banachModel_tensor_Acris l P AI T LL β hβ
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨by
    haveI := (P.PD K).finK₀
    exact Module.finrank_pos.ne'⟩
  let μ : ℕ → N := fun s => b ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (WittVector.teichmuller l (AI.εroot s) - 1))
  have hμ : ∀ s, Small (μ s) := hs
  have hc' : Bdd c := hc
  set_option synthInstance.maxHeartbeats 200000 in
  let f : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)) →+* N := b.comp I.io.toRingHom
  have hf : ∀ a, f a = b (I.io a) := fun _ => rfl
  have hfπ : f letπ = μ s := congrArg b I.io_π
  have hint : ∀ a, ev c (μ s) (map (algebraMap ↥(OL LL) ↥LL.1) a) = f (fun _ => a) := fun a =>
    ev_map (algebraMap ↥(OL LL) ↥LL.1) (hμ s) hc' (f.comp (Pi.constRingHom _ _))
      (fun o => (congrArg b (I.io.commutes o)).trans (by exact hbo o)) hfπ (fun _ => hb _) a (sc_map a)
  have hfφ : ∀ a, f (letφ R.φ₀ a) = φ (f a) := (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b (φ.comp b)).1 hφb
  have hfγ : ∀ (g : ↥(GK K)) a, f (letγ (R.γ₀ (Γ.resΓ g)) a) = γ g (f a) := fun g =>
    (GlobalTheory.T.wachInclusionLayer_io_commutes_frobenius_galois l P AI K s LL Γ R I N b ((γ g).comp b)).2 g (hγb g)
  have hsub : ∀ (ψ : N →+* N) (y : (↥(OL LL))⟦X⟧), Continuous ψ → (∀ x, ψ (c x) = c x) → constantCoeff y = 0 →
      f (fun _ => y) = ψ (μ s) → ∀ a, Conv a →
      ev c (μ s) (subst (map (algebraMap ↥(OL LL) ↥LL.1) y) a) = ψ (ev c (μ s) a) := by
    intro ψ y h1 h2 h3 h4 a ha
    have ha' := (conv_iff_sc a).1 ha
    have h5 := hasSum_subst hc' (hμ s) (y := map (algebraMap ↥(OL LL) ↥LL.1) y)
      (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h3, map_zero])
      (fun k => by simpa using norm_integer_le_one (coeff k y)) ha'
    rw [hint, h4] at h5
    exact h5.unique (hasSum_map hc' (hμ s) ha' ψ h1 h2)
  refine ⟨fun a => κ (∑ i, f (letE i) * ev c (μ s) (a i)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a' ha ha'
    rw [← map_add (f := _), ← Finset.sum_add_distrib]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.add_apply, ev_add hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i)), mul_add]
  · intro a a' ha ha'
    rw [← map_mul, ← sum_letE_mul]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.mul_apply, ev_mul hc' (hμ s) ((conv_iff_sc _).1 (ha i)) ((conv_iff_sc _).1 (ha' i))]
  · intro x a ha
    have e : algebraMap ↥LL.1 (↥LL.1 ⊗[ℚ_[l]] P.R.B) x = κ (c x) := (hκc x).symm
    rw [Algebra.smul_def x (κ _), e, ← map_mul, Finset.mul_sum]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Pi.smul_apply, ev_C_mul hc' (hμ s) x ((conv_iff_sc _).1 (ha i)), mul_left_comm]
  · intro a
    rw [← hκb, ← hf, ← sum_letE_const f a]
    exact congrArg κ (Finset.sum_congr rfl fun i _ => congrArg _ (hint (a i)))
  · intro a ha
    have hy : R.φ₀ X = (1 + X) ^ l - 1 := by rw [R.φ₀_X, R.q₀_def, P.PD_p]
    have hy' : ((1 + X) ^ l - 1 : (↥LL.1)⟦X⟧) = map (algebraMap ↥(OL LL) ↥LL.1) (R.φ₀ X) := by
      simp [hy]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hκφ, map_sum φ, ← Equiv.sum_comp (Equiv.subRight (1 : ZMod _))
      (fun i => φ (f (letE i) * ev c (μ s) (a i)))]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [Equiv.subRight_apply, map_mul, ← hfφ, letφ_letE, hy',
      hsub φ _ hφ hφc (by simp [hy]) (hfπ ▸ hfφ letπ) _ (ha _)]
  · intro g a ha
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hκγ, map_sum (γ g)]
    refine congrArg κ (Finset.sum_congr rfl fun i _ => ?_)
    rw [map_mul, ← hfγ, letγ_letE,
      hsub (γ g) _ (hγ g).1 (hγ g).2 (R.γ₀_X _).1 (hfπ ▸ hfγ g letπ) _ (ha _)]
  · rw [← Finset.sum_mul, sum_letE, one_mul]
    have key : ∀ k : ℕ, κ (ev c (μ k) (logS LL)) = (1 : ↥LL.1) ⊗ₜ[ℚ_[l]] ((((l : ℚ_[l]) ^ k)⁻¹) • P.tB) := by
      intro k
      induction k with
      | zero =>
        rw [tendsto_nhds_unique (hasSum_ev hc' (hμ 0) (sc_log LL)).tendsto_sum_nat hlog, hκt]
        simp
      | succ k ih =>
        have h1 := hasSum_map hc' (hμ (k + 1)) (sc_log LL) φ hφ hφc
        have h2 : φ (μ (k + 1)) = μ k := (hφb _ _).trans (by rw [frob_root])
        rw [h2] at h1
        apply frob_injective T LL
        have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
        rw [← hκφ, h1.unique (hasSum_ev hc' (hμ k) (sc_log LL)), ih, Algebra.TensorProduct.map_tmul, map_smul,
          crisFrobenius_periodT_eq_prime_smul P K, smul_smul, map_one, pow_succ, mul_inv, mul_assoc, inv_mul_cancel₀ hl, mul_one]
    exact key s
  · intro i ζ ι hι hζ a ha e he m
    let π : N →+* P.R.BdR := (Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp κ
    have hπ : ∀ x, π x = Algebra.TensorProduct.productMap ι P.ιB (κ x) := fun _ => rfl
    have hπc : ∀ x, π (c x) = ι x := fun x => by rw [hπ, hκc]; simp
    have hπE : ∀ j, π (f (letE j)) = if i = j then 1 else 0 := fun j => by
      have h := GlobalTheory.T.productMap_tensorAinfToBcris_wachInclusion_constants l P AI T K s LL hG Γ R I hW β hβ i ι hι (Pi.single j 1)
      have e1 : (fun k => C ((Pi.single j 1 : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL)) k)) =
          (letE j : LetA ↥(OL LL) _) := by
        ext1 k
        by_cases h : k = j <;> simp [letE, h]
      rw [e1] at h
      rw [hπ, hf, hκb, h]
      by_cases h : i = j <;> simp [h]
    have hπμ : π (μ s) = P.ιB (AI.ιA (WittVector.teichmuller l (AI.εroot s) - 1)) := by
      rw [hπ, hκb, hβ]
      simp
    let τ : N := c (algebraMap ℚ_[l] ↥LL.1 ((l : ℚ_[l]) ^ s)⁻¹) * t
    have hπτ : π τ = (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB := by
      rw [map_mul, hπc, AlgHom.commutes, hπ, hκt, Algebra.smul_def]
      simp
    have hev : ∀ x : ℕ → ↥LL.1, π (∑ k ∈ Finset.range m, c (x k) * τ ^ k) =
        ∑ k ∈ Finset.range m, ι (x k) * ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB) ^ k := fun x => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul π, map_pow π, hπc, hπτ]
    have hlim : Tendsto (fun M : ℕ => Polynomial.eval₂ c (μ s) (trunc M (a i)) - ∑ k ∈ Finset.range m,
        c (coeff k (Polynomial.aeval (C ζ * exp ↥LL.1 - 1) (trunc M (a i)))) * τ ^ k) atTop
        (nhds (ev c (μ s) (a i) - ∑ k ∈ Finset.range m, c (coeff k e) * τ ^ k)) := by
      refine (tendsto_ev hc' (hμ s) ((conv_iff_sc _).1 (ha i))).sub (tendsto_finsetSum _ fun k _ => ?_)
      exact ((hc'.continuous.tendsto _).comp (tendsto_subtype_rng.2 (he k))).mul_const _
    have hmem := (hcl ι m).mem_of_tendsto hlim (Eventually.of_forall fun M => by
      have h := GlobalTheory.T.polynomial_teichmullerRoot_taylor_modFil l P AI T LL s ζ ι hζ (trunc M (a i)) m
      rw [Set.mem_setOf_eq, ← hπ, map_sub, hev, Polynomial.hom_eval₂, hπμ, show π.comp c = (ι : ↥LL.1 →+* P.R.BdR) from RingHom.ext hπc]
      exact h)
    rw [Set.mem_setOf_eq, ← hπ, map_sub, hev] at hmem
    have e2 : π (∑ j, f (letE j) * ev c (μ s) (a j)) = π (ev c (μ s) (a i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, map_mul π, hπE]
    rw [← hπ, e2]
    exact (Set.ext_iff.1 (P.PD_Fil _ K m) _).1 hmem

end GlobalTheory.HWL.BanachEval
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEvaluationConvergentSeriesBcrisStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evaluation_convergent_series_Bcris : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∃ J, IsEval I β J := by
  first | exact @GlobalTheory.HWL.BanachEval.exists_eval | exact GlobalTheory.HWL.BanachEval.exists_eval | (intros; apply GlobalTheory.HWL.BanachEval.exists_eval <;> assumption)
end
