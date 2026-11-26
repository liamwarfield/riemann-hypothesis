module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceCompactTorusClassesCompactWeylCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PacketSumSignCastNeZero
open Finset

namespace GlobalTheory

lemma packetSum_vdm_eq_det {r : ℕ} (β : Fin r → ℂ) :
    Formalism.PacketSums.vdm β = (∏ i : Fin r, ∏ _j ∈ Ioi i, (-1 : ℂ)) * (Matrix.vandermonde β).det := by
  rw [Matrix.det_vandermonde, ← Finset.prod_mul_distrib]
  unfold Formalism.PacketSums.vdm
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_mul_distrib]
  have : Finset.univ.filter (fun j => i < j) = Ioi i := by ext; simp
  rw [this]
  refine Finset.prod_congr rfl fun j _ => ?_
  ring

lemma packetSum_vdm_perm {r : ℕ} (α : Fin r → ℂ) (σ : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.vdm (fun i => α (σ i)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * Formalism.PacketSums.vdm α := by
  rw [packetSum_vdm_eq_det, packetSum_vdm_eq_det]
  have : Matrix.vandermonde (fun i => α (σ i)) = (Matrix.vandermonde α).submatrix σ id := by
    ext i j; simp [Matrix.vandermonde_apply]
  rw [this, Matrix.det_permute]
  ring

lemma packetSum_sign_cast_ne_zero {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    ((Equiv.Perm.sign σ : ℤ) : ℂ) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma packetSum_numK_perm {r : ℕ} (WK : Subgroup (Equiv.Perm (Fin r))) [Fintype WK]
    (μ : Fin r → ℤ) (α : Fin r → ℂ) (y : Equiv.Perm (Fin r)) :
    Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) =
      ((Equiv.Perm.sign y : ℤ) : ℂ) * ∑ w : WK,
        ((Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) : ℤ) : ℂ) *
          ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
  unfold Formalism.PacketSums.numK
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hp : ∏ i, α (y⁻¹ i) ^ μ ((w : Equiv.Perm (Fin r))⁻¹ i) =
      ∏ j, α j ^ μ ((y⁻¹ * (w : Equiv.Perm (Fin r)))⁻¹ j) := by
    rw [← Equiv.prod_comp y]
    simp [mul_inv_rev, Equiv.Perm.mul_apply]
  rw [hp, ← mul_assoc]
  congr 1
  have hs : Equiv.Perm.sign (w : Equiv.Perm (Fin r)) =
      Equiv.Perm.sign y * Equiv.Perm.sign (y⁻¹ * (w : Equiv.Perm (Fin r))) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, ← mul_assoc, Int.units_mul_self, one_mul]
  rw [hs]; push_cast; ring

theorem packetSum : Formalism.PacketSums.PacketSum := by
  intro r WK _ T hbij μ α _ _
  set f : Equiv.Perm (Fin r) → ℂ := fun σ =>
    ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, α j ^ μ (σ⁻¹ j) with hf
  have hterm : ∀ y : Equiv.Perm (Fin r),
      Formalism.PacketSums.numK WK μ (fun i => α (y⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α (y⁻¹ i)) =
        (∑ w : WK, f (y⁻¹ * (w : Equiv.Perm (Fin r)))) / Formalism.PacketSums.vdm α := by
    intro y
    rw [packetSum_numK_perm, packetSum_vdm_perm α y⁻¹, Equiv.Perm.sign_inv,
      mul_div_mul_left _ _ (packetSum_sign_cast_ne_zero y)]
  rw [Finset.sum_congr rfl fun y _ => hterm y, ← Finset.sum_div]
  congr 1
  rw [← Finset.sum_coe_sort T]
  rw [← Fintype.sum_bijective _ hbij (fun p : WK × T => f ((p.2 : Equiv.Perm (Fin r))⁻¹ * p.1)) f
    (fun _ => rfl)]
  rw [Fintype.sum_prod_type_right]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SignEven
namespace GlobalTheory

theorem signEven : Formalism.PacketSums.SignEven := by
  intro p q h
  apply Even.neg_one_pow
  rw [Nat.even_mul]
  rcases Nat.even_or_odd p with hp | hp
  · exact Or.inl hp
  · right
    rcases Nat.even_or_odd q with hq | hq
    · exact hq
    · exact absurd (hp.add_odd hq) (Nat.not_even_iff_odd.mpr h)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactWeyl
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
open GlobalTheory.TrEll

noncomputable section
namespace GlobalTheory.RealSigns

def weylSub {n : ℕ} (ε : Fin n → Bool) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {w | ε ∘ ⇑w = ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ha, hb]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← ha]
    ext i; simp

theorem mem_weylSub {n : ℕ} (ε : Fin n → Bool) (w : Equiv.Perm (Fin n)) :
    w ∈ weylSub ε ↔ w ∈ GlobalTheory.HCChar.compactWeyl ε := by
  simp [weylSub, GlobalTheory.HCChar.compactWeyl]

theorem of_cosets (hR : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau), CompactSpace (Tor P (placeOf D ρ).Completion) → ∀ WK : Subgroup (Equiv.Perm (Fin V.rank)), (∀ w, w ∈ WK ↔ w ∈ GlobalTheory.HCChar.compactWeyl (M.ε ρ)) → ∃ (T : Finset (Equiv.Perm (Fin V.rank))) (b : XSet P (placeOf D ρ).Completion V.gram ≃ T), Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin V.rank)))⁻¹ * (p.1 : Equiv.Perm (Fin V.rank))) ∧ ∀ (q : XSet P (placeOf D ρ).Completion V.gram) (γ : GArch D.sp.cm.sig V.gram (placeOf D ρ)), HasCls P (placeOf D ρ).Completion V.gram γ q.1 → ∃ g, frameMat M ρ (g * γ * g⁻¹) = Matrix.diagonal fun i => cxRoots (embOverOf D ρ).1 P ((b q : Equiv.Perm (Fin V.rank))⁻¹ i)) : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  intro D V S M ρ P hc
  have hR' := hR D V S M P ρ hc (weylSub (M.ε ρ)) (mem_weylSub (M.ε ρ))
  obtain ⟨T, b, hbij, hconj⟩ := hR'
  have hfin : (XSet P (placeOf D ρ).Completion V.gram).Finite :=
    Set.finite_coe_iff.1 (Finite.of_equiv _ b.symm)
  have h1 := @GlobalTheory.T.compact_unitaryTorus_real_place_tensor_eq_complex_pow D.host.F D.host.E _ _ _ _ _ D.sp.cm.sig (GlobalTheory.AdelicU.isCMExt_host D) V.rank P
    (placeOf D ρ) (embOverOf D ρ)
  have hnorm : ∀ i, ‖cxRoots (embOverOf D ρ).1 P i‖ = 1 := by
    obtain ⟨Ψ, h3⟩ := h1 (by convert hc using 0)
    exact h3.2.2.2.2.2
  have hexp : ∀ z : ℂ, ‖z‖ = 1 → Complex.exp (Complex.arg z * Complex.I) = z := fun z hz => by
    have h := Complex.norm_mul_exp_arg_mul_I z
    rwa [hz, Complex.ofReal_one, one_mul] at h
  refine ⟨hfin, fun q => (b q : Equiv.Perm (Fin V.rank)),
    fun q a => Complex.arg (cxRoots (embOverOf D ρ).1 P (((b q : Equiv.Perm (Fin V.rank)))⁻¹ a)), ?_,
    fun q a => hexp _ (hnorm _), ?_⟩
  · let e : GlobalTheory.HCChar.compactWeyl (M.ε ρ) ≃ weylSub (M.ε ρ) :=
      { toFun := fun w => ⟨w.1, (mem_weylSub _ _).2 w.2⟩, invFun := fun w => ⟨w.1, (mem_weylSub _ _).1 w.2⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    exact hbij.comp (Equiv.prodCongr e b).bijective
  · intro q
    have hq : HasCls P (placeOf D ρ).Completion V.gram (gam q.2.choose_spec.choose_spec.2) q.1 :=
      ⟨_, _, q.2.choose_spec.choose_spec.2, q.2.choose_spec.choose_spec.1, rfl⟩
    have hc2 := hconj q (gam q.2.choose_spec.choose_spec.2) hq
    obtain ⟨g, hg⟩ := hc2
    refine ⟨g⁻¹, (congrArg (fun h => frameMat M ρ (h * gam q.2.choose_spec.choose_spec.2 * g⁻¹)) (inv_inv g)).trans (hg.trans ?_)⟩
    exact congrArg Matrix.diagonal (funext fun a => (hexp _ (hnorm _)).symm)

end GlobalTheory.RealSigns
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectors
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section
namespace GlobalTheory.RealSigns

theorem signs_real : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) :=
  of_cosets GlobalTheory.T.real_place_compact_torus_classes_compactWeyl_cosets

end GlobalTheory.RealSigns
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRealPlaceTorusClassesSignVectorsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactRealPlace_torusClasses_signVectors : ∀ {D : D7} (V : HSp D) {S : D.what₂.Tau → SPar} (M : DSModel V S) (ρ : D.what₂.Tau)
    (P : PPol D.sp.cm.sig V.rank), CompactSpace (Tor P (placeOf D ρ).Completion) →
    (XSet P (placeOf D ρ).Completion V.gram).Finite ∧
      ∃ (y : XSet P (placeOf D ρ).Completion V.gram → Equiv.Perm (Fin V.rank))
        (θ : XSet P (placeOf D ρ).Completion V.gram → Fin V.rank → ℝ),
        Function.Bijective (fun p : compactWeyl (M.ε ρ) × XSet P (placeOf D ρ).Completion V.gram =>
          (y p.2)⁻¹ * p.1.1) ∧
        (∀ q a, Complex.exp (θ q a * Complex.I) = cxRoots (embOverOf D ρ).1 P ((y q)⁻¹ a)) ∧
        ∀ q, ∃ g : GArch D.sp.cm.sig V.gram (placeOf D ρ), frameMat M ρ (g⁻¹ * gam q.2.choose_spec.choose_spec.2 * g) =
          Matrix.diagonal fun a => Complex.exp (θ q a * Complex.I) := by
  first | exact @GlobalTheory.RealSigns.signs_real | exact GlobalTheory.RealSigns.signs_real | (intros; apply GlobalTheory.RealSigns.signs_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.RealPlaceCentraliser

section Gen
open scoped Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} {P : PPol σ r}
  {k : Type} [Field k] [Algebra F k] {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem nondeg (hJ : IsHermND σ J) (b : Fin n → k ⊗[F] E)
    (hb : ∀ a, Formalism.UG.hform (sigR k σ) (JR k J) a b = 0) : b = 0 := by
  have hv : JR (F := F) k J *ᵥ b = 0 := by
    funext i
    have := hb (Pi.single i 1)
    simpa [Formalism.UG.hform, Pi.single_apply, Matrix.mulVec, dotProduct] using this
  have hdet : IsUnit (JR (F := F) k J).det := by
    have : (JR (F := F) k J).det = inclR (F := F) k J.det := by
      rw [RingHom.map_det]; rfl
    rw [this]
    exact (isUnit_iff_ne_zero.mpr hJ.2).map _
  calc b = ((JR (F := F) k J)⁻¹ * JR (F := F) k J) *ᵥ b := by rw [Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem zero_of_hx (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) (z : k ⊗[F] Fld P)
    (hz : ∀ y', hx P k x z y' = 0) : z = 0 := by
  have : φ z = 0 := nondeg hJ _ fun a => by
    obtain ⟨y', rfl⟩ := φ.surjective a
    rw [h]; exact hz y'
  simpa using this

theorem isUnit_of_isIsom [Module.Finite F (Fld P)] (hJ : IsHermND σ J) {x : k ⊗[F] Fld P}
    {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) : IsUnit x := by
  haveI : Module.Finite k (k ⊗[F] Fld P) := Module.Finite.base_change F k (Fld P)
  have hinj : Function.Injective (LinearMap.mulLeft k x) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    refine zero_of_hx hJ h y fun y' => ?_
    simp only [LinearMap.mulLeft_apply] at hy
    simp [hx, hy]
  obtain ⟨y, hy⟩ := LinearMap.injective_iff_surjective.mp hinj 1
  exact isUnit_iff_exists_inv.mpr ⟨y, hy⟩

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] E) : sigR k σ (sigR k σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem hform_herm (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J) (a b : Fin n → k ⊗[F] E) :
    sigR k σ (Formalism.UG.hform (sigR k σ) (JR k J) a b) = Formalism.UG.hform (sigR k σ) (JR k J) b a := by
  have hG : ∀ i j, sigR k σ (JR (F := F) k J i j) = JR (F := F) k J j i := by
    intro i j
    simp only [JR, Matrix.map_apply, inclR]
    change sigR k σ (1 ⊗ₜ J i j) = 1 ⊗ₜ J j i
    simp [sigR, hJ.1]
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem trace_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (l : Fld P) :
    Algebra.trace E (Fld P) (star' P l) = σ (Algebra.trace E (Fld P) l) := by
  let e₁ : E ≃+* E := RingEquiv.ofBijective σ (Function.Involutive.bijective hσ)
  let e₂ : Fld P ≃+* Fld P := RingEquiv.ofBijective (star' P) (Algebra.IsAlgebraic.algHom_bijective _)
  have he : (algebraMap E (Fld P)).comp (e₁ : E →+* E) = (e₂ : Fld P →+* Fld P).comp (algebraMap E (Fld P)) :=
    RingHom.ext fun e => (star'_algebraMap P e).symm
  have := Algebra.trace_eq_of_equiv_equiv e₁ e₂ he l
  have h2 := congrArg e₁ this
  rw [RingEquiv.apply_symm_apply] at h2
  exact h2.symm

theorem trBase_star [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (z : k ⊗[F] Fld P) :
    trBase P k (sigR k (star' P) z) = sigR k σ (trBase P k z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a l => simp [trBase, sigR, trace_star hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem plusUnits_gen [Module.Finite F (Fld P)] (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    {x : k ⊗[F] Fld P} {φ : (k ⊗[F] Fld P) ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ∃ u : plusUnits P k, u.1.1 = x := by
  have hu := isUnit_of_isIsom hJ h
  have hsym : ∀ y, trBase P k ((x - sigR k (star' P) x) * sigR k (star' P) y) = 0 := by
    intro y
    have h1 := h 1 y
    have h2 := h y 1
    have h3 := hform_herm hσ hJ (φ 1) (φ y)
    rw [h2, h1] at h3
    simp only [hx, map_one, mul_one] at h3
    rw [← trBase_star hσ, map_mul] at h3
    rw [sub_mul, map_sub, ← h3, sub_self]
  have hd : x - sigR k (star' P) x = 0 := by
    obtain ⟨v, hv⟩ := hu
    have h0 := zero_of_hx hJ h (↑v⁻¹ * (x - sigR k (star' P) x)) fun y' => by
      simp only [hx]
      rw [show x * (↑v⁻¹ * (x - sigR k (star' P) x)) * sigR k (star' P) y' =
          (x - sigR k (star' P) x) * sigR k (star' P) y' by
        rw [← mul_assoc, ← hv, Units.mul_inv, one_mul]]
      exact hsym y'
    have := congrArg (fun w => (v : k ⊗[F] Fld P) * w) h0
    simpa [← mul_assoc] using this
  refine ⟨⟨hu.unit, ?_⟩, rfl⟩
  show Units.map (sigR k (star' P)).toMonoidHom hu.unit = MonoidHom.id _ hu.unit
  ext
  simpa using (sub_eq_zero.mp hd).symm

end Gen

theorem plusUnits_of_isIsom {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) :
    ∃ u : plusUnits P (placeOf D ρ).Completion, u.1.1 = x := by
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  exact plusUnits_gen (fun e => star_star e) (GlobalTheory.DefiniteQuotient.gram_hermND V) h

theorem topGrp {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    IsTopologicalGroup (HA R σ J) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact inferInstanceAs (IsTopologicalGroup (HR R σ J))

theorem borel {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    BorelSpace (HA R σ J) := ⟨rfl⟩

theorem torComm {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) (J : Matrix (Fin 1) (Fin 1) E) (s t : HA R σ J) : s * t = t * s := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi hj
  change (s.1.1 * t.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0 = (t.1.1 * s.1.1 : Matrix (Fin 1) (Fin 1) _) 0 0
  simp [Matrix.mul_apply, mul_comm]

theorem measFacts {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (hc : ∀ a b : G, a * b = b * a) (e : G ≃ₜ* H) (dt : Measure G) [dt.IsHaarMeasure] :
    (dt.map e).IsHaarMeasure ∧ (dt.map e).IsMulRightInvariant ∧ (dt.map e).real univ = dt.real univ ∧
      (CompactSpace H ↔ CompactSpace G) := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have := congrArg e (hc (e.symm a) (e.symm b))
    simpa [map_mul] using this
  haveI hH : (dt.map e).IsHaarMeasure := e.isHaarMeasure_map dt
  refine ⟨hH, ⟨fun g => ?_⟩, ?_, ?_⟩
  · have : (fun a : H => a * g) = (fun a => g * a) := funext fun a => hcomm a g
    rw [this]
    exact map_mul_left_eq_self _ g
  · rw [Measure.real, Measure.real, Measure.map_apply (show Measurable (e : G → H) from e.continuous.measurable) MeasurableSet.univ, Set.preimage_univ]
  · exact ⟨fun hc => e.toHomeomorph.symm.compactSpace, fun hc => e.toHomeomorph.compactSpace⟩

theorem centMeas_real_place : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  intro D V P ρ dt _ x φ h
  obtain ⟨u, rfl⟩ := plusUnits_of_isIsom V P ρ h
  have H := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure D.host.F D.host.E D.sp.cm.sig (GlobalTheory.DefiniteQuotient.cmExt D) V.rank V.rank P V.gram
    (GlobalTheory.DefiniteQuotient.gram_hermND V) (placeOf D ρ).Completion u φ h
  obtain ⟨e, H2⟩ := H
  have hm := H2.2
  haveI : Module.Finite D.host.F D.host.E := inferInstance
  haveI : Module.Finite D.host.F (Fld P) := Module.Finite.trans D.host.E (Fld P)
  haveI := topGrp (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := topGrp (placeOf D ρ).Completion (star' P) (one₁ P)
  haveI := borel (placeOf D ρ).Completion D.sp.cm.sig V.gram
  haveI := borel (placeOf D ρ).Completion (star' P) (one₁ P)

  simp only [hm dt]
  have hc := torComm (placeOf D ρ).Completion (star' P) (one₁ P)
  have hf := measFacts (G := Tor P (placeOf D ρ).Completion) (H := cent (gam h)) hc e dt
  refine ⟨hf.1, hf.2.1, hf.2.2.1, ?_⟩
  rw [isCompact_iff_compactSpace]
  exact hf.2.2.2

end GlobalTheory.RealPlaceCentraliser
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerTorusEllipticElementRealPlaceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_torusEllipticElement_realPlace : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau)
    (dt : Measure (Tor P (placeOf D ρ).Completion)) [dt.IsHaarMeasure] {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ),
    (centMeas h dt).IsHaarMeasure ∧ (centMeas h dt).IsMulRightInvariant ∧
      (centMeas h dt).real univ = dt.real univ ∧
      (IsCompact (cent (gam h) : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) ↔
        CompactSpace (Tor P (placeOf D ρ).Completion)) := by
  first | exact @GlobalTheory.RealPlaceCentraliser.centMeas_real_place | exact GlobalTheory.RealPlaceCentraliser.centMeas_real_place | (intros; apply GlobalTheory.RealPlaceCentraliser.centMeas_real_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacter
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacter
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.WeylPacket

theorem det_rev_pow_eq_vdm {r : ℕ} (a : Fin r → ℂ) :
    (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)).det = Formalism.PacketSums.vdm a := by
  have h2 : (Matrix.of fun i j : Fin r => a i ^ (j.rev : ℕ)) =
      (Matrix.vandermonde (a ∘ Fin.revPerm)).submatrix Fin.revPerm Fin.revPerm := by
    ext i j
    simp [Matrix.vandermonde_apply, Fin.rev_rev]
  have key : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.Ioi i, f i j = ∏ i, ∏ j, if i < j then f i j else 1 := by
    intro f
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext j
    simp
  have key2 : ∀ f : Fin r → Fin r → ℂ,
      ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), f i j = ∏ i, ∏ j, if i < j then f i j else 1 :=
    fun f => Finset.prod_congr rfl fun i _ => Finset.prod_filter _ _
  rw [h2, Matrix.det_submatrix_equiv_self, Matrix.det_vandermonde, Formalism.PacketSums.vdm, key, key2, Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ fun j => ?_
  refine Fintype.prod_equiv Fin.revPerm _ _ fun i => ?_
  simp [Fin.rev_lt_rev]

theorem det_zpow_eq_sum {r : ℕ} (a : Fin r → ℂ) (m : Fin r → ℤ) :
    (Matrix.of fun i j : Fin r => a i ^ m j).det =
      ∑ w : Equiv.Perm (Fin r), ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, a i ^ m (w⁻¹ i) := by
  rw [Matrix.det_apply']
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 1
  exact Fintype.prod_equiv w _ _ fun i => by simp

end GlobalTheory.WeylPacket


open GlobalTheory.WeylPacket in
theorem GlobalTheory.dsChar_finsum_eq_glChar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  intro n ε lam α ι _ y θ hn hα hb hθ
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨k, hk⟩ := id hn
  set m : Fin n → ℤ := fun a => lam a + (((n - 1) / 2 : ℕ) : ℤ) with hmdef
  have hk2 : (n - 1) / 2 = k := by omega
  have hm : ∀ a, ((fun a => (lam a : ℝ)) a) + ((n : ℝ) - 1) / 2 = (m a : ℝ) := by
    intro a
    have hn' : (n : ℝ) = 2 * k + 1 := by exact_mod_cast hk
    simp only [hmdef, hk2, hn']
    push_cast
    ring
  let WK : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {w | ε ∘ w = ε}
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        funext x
        have ha' := congrFun ha (b x)
        have hb' := congrFun hb x
        simp only [Function.comp_apply] at ha' hb' ⊢
        rw [Equiv.Perm.mul_apply, ha', hb']
      one_mem' := by simp
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at *
        funext x
        have := congrFun ha (a⁻¹ x)
        simp only [Function.comp_apply] at this ⊢
        rw [show a (a⁻¹ x) = x from by simp] at this
        exact this.symm }
  haveI : Fintype WK := Fintype.ofFinite _
  have hmem : ∀ w, w ∈ WK ↔ w ∈ compactWeyl ε := by
    intro w
    show ε ∘ w = ε ↔ _
    simp [compactWeyl]
  have h1 : (1 : Equiv.Perm (Fin n)) ∈ compactWeyl ε := by simp [compactWeyl]
  have hy : Function.Injective y := by
    intro q q' h
    have := hb.1 (a₁ := (⟨1, h1⟩, q)) (a₂ := (⟨1, h1⟩, q')) (by simp [h])
    exact congrArg Prod.snd this
  have hα0 : ∀ i, α i ≠ 0 := by
    intro i
    obtain ⟨⟨w, q⟩, -⟩ := hb.2 1
    have := hθ q (y q i)
    rw [show (y q)⁻¹ (y q i) = i from by simp] at this
    rw [← this]
    exact Complex.exp_ne_zero _
  set T : Finset (Equiv.Perm (Fin n)) := Finset.univ.image y with hT
  let eT : ι ≃ T := Equiv.ofBijective (fun q => ⟨y q, Finset.mem_image_of_mem _ (Finset.mem_univ q)⟩)
    ⟨fun q q' h => hy (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hg
      exact ⟨q, rfl⟩⟩
  let e : compactWeyl ε × ι ≃ WK × T :=
    Equiv.prodCongr (Equiv.subtypeEquivRight fun w => (hmem w).symm) eT
  have hbij : Function.Bijective (fun p : WK × T => ((p.2 : Equiv.Perm (Fin n)))⁻¹ * (p.1 : Equiv.Perm (Fin n))) :=
    (Equiv.bijective_comp e _).1 hb
  have hPS := GlobalTheory.packetSum n WK T hbij m α hα0 hα
  have hsign : (-1 : ℂ) ^ halfDim ε = 1 := by
    have hpq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun a : Fin n => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at hpq
    have := GlobalTheory.signEven _ _ (by rw [hpq]; exact hn)
    rw [halfDim]
    exact_mod_cast this
  have hterm : ∀ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) =
      Formalism.PacketSums.numK WK m (fun i => α ((y q)⁻¹ i)) / Formalism.PacketSums.vdm (fun i => α ((y q)⁻¹ i)) := by
    intro q
    rw [dsChar_eq ε hm (θ q), hsign, one_mul]
    simp only [hθ q]
    congr 1
    · rw [Formalism.PacketSums.numK, Finset.sum_subtype (compactWeyl ε) (fun w => (hmem w).symm)]
      rfl
    · rw [Formalism.PacketSums.vdm]
      exact Finset.prod_congr rfl fun i _ => Finset.prod_congr (by ext j; simp) fun _ _ => rfl
  have hexp : ∀ j : Fin n, hiWt lam j + ((j.rev : ℕ) : ℤ) = m j := by
    intro j
    have := j.isLt
    simp only [hiWt, hmdef, Fin.val_rev]
    omega
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl fun q _ => hterm q,
    ← Finset.sum_image (f := fun g : Equiv.Perm (Fin n) => Formalism.PacketSums.numK WK m (fun i => α (g⁻¹ i)) /
      Formalism.PacketSums.vdm (fun i => α (g⁻¹ i))) (fun q _ q' _ h => hy h), ← hT, hPS, glChar, det_rev_pow_eq_vdm,
    ← det_zpow_eq_sum]
  congr 2
  ext i j
  simp only [Matrix.of_apply, hexp j]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDiscreteSeriesCharacterEqWeylCharacterStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_discreteSeriesCharacter_eq_weylCharacter : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℤ) (α : Fin n → ℂ) (ι : Type) [Finite ι]
    (y : ι → Equiv.Perm (Fin n)) (θ : ι → Fin n → ℝ), Odd n → Function.Injective α →
    Function.Bijective (fun p : compactWeyl ε × ι => (y p.2)⁻¹ * p.1.1) →
    (∀ q a, Complex.exp (θ q a * Complex.I) = α ((y q)⁻¹ a)) →
    ∑ᶠ q, dsChar ε (fun a => (lam a : ℝ)) (θ q) = glChar (hiWt lam) α := by
  first | exact @GlobalTheory.dsChar_finsum_eq_glChar | exact GlobalTheory.dsChar_finsum_eq_glChar | (intros; apply GlobalTheory.dsChar_finsum_eq_glChar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlace
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

noncomputable section

namespace GlobalTheory.RegularGamma

open Polynomial

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)
  (k : Type) [CommRing k] [Algebra F k]

abbrev pbL : PowerBasis E (Fld P) := AdjoinRoot.powerBasis P.2.2.1.ne_zero

def vec : Fin (pbL P).dim → k ⊗[F] Fld P := fun i => (1 : k) ⊗ₜ (pbL P).basis i

theorem smul_tmul' (a : k) (e : E) (b : k) (l : Fld P) :
    (a ⊗ₜ[F] e : k ⊗[F] E) • (b ⊗ₜ[F] l : k ⊗[F] Fld P) = (a * b) ⊗ₜ (algebraMap E (Fld P) e * l) := by
  rw [Algebra.smul_def]
  change (Algebra.TensorProduct.map (AlgHom.id F k) (IsScalarTower.toAlgHom F E (Fld P))) (a ⊗ₜ[F] e) * _ = _
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  rfl

theorem span_vec : Submodule.span (k ⊗[F] E) (Set.range (vec P k)) = ⊤ := by
  refine Submodule.eq_top_iff'.2 fun t => ?_
  induction t using TensorProduct.induction_on with
  | zero => exact zero_mem _
  | add x y hx hy => exact add_mem hx hy
  | tmul a l =>
    rw [← (pbL P).basis.sum_repr l, TensorProduct.tmul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : a ⊗ₜ[F] ((pbL P).basis.repr l i • (pbL P).basis i) =
        (a ⊗ₜ[F] (pbL P).basis.repr l i : k ⊗[F] E) • vec P k i := by
      rw [vec, smul_tmul', mul_one, Algebra.smul_def]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem bijective_vec (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Function.Bijective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
  have hs : Function.Surjective (Fintype.linearCombination (k ⊗[F] E) (vec P k)) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, span_vec]
  have hd : (pbL P).dim = r := (AdjoinRoot.powerBasis_dim _).trans P.2.2.2.1
  let ψ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin (pbL P).dim → k ⊗[F] E) :=
    φ.trans (LinearEquiv.funCongrLeft _ _ (finCongr hd))
  haveI : Module.Finite (k ⊗[F] E) (k ⊗[F] Fld P) := Module.Finite.equiv φ.symm
  have hi := OrzechProperty.injective_of_surjective_endomorphism
    ((Fintype.linearCombination (k ⊗[F] E) (vec P k)) ∘ₗ ψ.toLinearMap) (hs.comp ψ.surjective)
  refine ⟨fun y y' hyy => ?_, hs⟩
  obtain ⟨z, rfl⟩ := ψ.surjective y
  obtain ⟨z', rfl⟩ := ψ.surjective y'
  rw [hi hyy]

def bas (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    Module.Basis (Fin (pbL P).dim) (k ⊗[F] E) (k ⊗[F] Fld P) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (bijective_vec P k φ)).symm

theorem bas_apply (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) (i : Fin (pbL P).dim) :
    bas P k φ i = vec P k i := by
  simp [bas, Module.Basis.coe_ofEquivFun]

theorem mul_vec (j : Fin (pbL P).dim) :
    ((1 : k) ⊗ₜ[F] alpha P) * vec P k j =
      ∑ i, (inclR (F := F) k (Algebra.leftMulMatrix (pbL P).basis (alpha P) i j)) • vec P k i := by
  have hinc : ∀ e : E, inclR (F := F) k e = (1 : k) ⊗ₜ[F] e := fun _ => rfl
  simp only [vec, hinc, smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← TensorProduct.tmul_sum]
  congr 1
  simp only [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', ← Algebra.smul_def]
  exact ((pbL P).basis.sum_repr _).symm

theorem charpoly_mul_alpha (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    haveI := Module.Free.of_basis (bas P k φ)
    haveI := Module.Finite.of_basis (bas P k φ)
    (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  rw [← LinearMap.charpoly_toMatrix _ (bas P k φ)]
  have hM : LinearMap.toMatrix (bas P k φ) (bas P k φ)
      (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)) =
      (Algebra.leftMulMatrix (pbL P).basis (alpha P)).map (inclR (F := F) k) := by
    ext i j
    rw [LinearMap.toMatrix_apply, LinearMap.mul_apply', bas_apply, mul_vec]
    simp_rw [← bas_apply P k φ]
    rw [Module.Basis.repr_sum_self]
    rfl
  rw [hM, Matrix.charpoly_map, show alpha P = (pbL P).gen from (AdjoinRoot.powerBasis_gen _).symm,
    charpoly_leftMulMatrix]
  exact congrArg _ (AdjoinRoot.minpoly_powerBasis_gen_of_monic P.2.1)

theorem charpoly_mulMat (φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin r → k ⊗[F] E)) :
    (mulMat φ ((1 : k) ⊗ₜ[F] alpha P)).charpoly = P.1.map (inclR (F := F) k) := by
  haveI := Module.Free.of_basis (bas P k φ)
  haveI := Module.Finite.of_basis (bas P k φ)
  change (LinearMap.toMatrix' (φ.conj (LinearMap.mul (k ⊗[F] E) (k ⊗[F] Fld P) ((1 : k) ⊗ₜ[F] alpha P)))).charpoly = _
  rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix, LinearEquiv.charpoly_conj,
    charpoly_mul_alpha P k φ]

variable {P k}

theorem gam_val {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {x : k ⊗[F] Fld P}
    {φ : k ⊗[F] Fld P ≃ₗ[k ⊗[F] E] (Fin n → k ⊗[F] E)} (h : IsIsom P k J x φ) :
    ((gam h).1 : Matrix (Fin n) (Fin n) (k ⊗[F] E)) = mulMat φ ((1 : k) ⊗ₜ[F] alpha P) := by
  change mulMat φ (torUnit _).1 = _
  congr 1
  change Matrix.det _ = _
  rw [Matrix.det_fin_one]
  rfl

end GlobalTheory.RegularGamma

namespace GlobalTheory.RegularGamma

open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots

theorem isRegSS_gam {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ) : IsRegSS (matAt V ρ (gam h)) := by
  have hm : matAt V ρ (gam h) = (mulMat φ ((1 : (placeOf D ρ).Completion) ⊗ₜ alpha P)).map (infEmb (embOverOf D ρ)) := by
    rw [← gam_val h]
    rfl
  change (matAt V ρ (gam h)).charpoly.Separable
  rw [hm, Matrix.charpoly_map, charpoly_mulMat, Polynomial.map_map]
  exact (Irreducible.separable P.2.2.1).map

end GlobalTheory.RegularGamma
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularSemisimpleTorusEllipticElementRealPlaceStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularSemisimple_torusEllipticElement_realPlace : ∀ {D : D7} (V : HSp D) (P : PPol D.sp.cm.sig V.rank) (ρ : D.what₂.Tau) {x φ}
    (h : IsIsom P (placeOf D ρ).Completion V.gram x φ), IsRegSS (matAt V ρ (gam h)) := by
  first | exact @GlobalTheory.RegularGamma.isRegSS_gam | exact GlobalTheory.RegularGamma.isRegSS_gam | (intros; apply GlobalTheory.RegularGamma.isRegSS_gam <;> assumption)
end
end

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.TrMult


end GlobalTheory.TrMult
