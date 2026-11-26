module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlobalArtinReciprocityHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeCentralizerComm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
noncomputable section

open ValuativeRel
open scoped Topology
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

namespace GlobalTheory.LocLanglands

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem valuation_le_iff_ord {x y : kˣ} : valuation k (x : k) ≤ valuation k (y : k) ↔ ord k y ≤ ord k x := by
  rw [ord, ord, neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp)]
  exact (map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k)).symm

theorem valuation_eq_iff_ord {x y : kˣ} : valuation k (x : k) = valuation k (y : k) ↔ ord k x = ord k y := by
  rw [le_antisymm_iff, valuation_le_iff_ord, valuation_le_iff_ord]; omega

variable (k) in
theorem exists_unit_pow (a : ℕ) : ∃ p : kˣ, valuation k (p : k) = uniformizer k ^ a ∧ ord k p = a := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer k)
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact uniformizer_ne_zero (R := k) (by simpa using hy.symm)
  have h1 : ord k (Units.mk0 y hy0) = 1 := ord_eq_one hy
  refine ⟨Units.mk0 y hy0 ^ a, by simp [hy], ?_⟩
  induction a with
  | zero => simpa using ord_eq_zero (k := k) (x := 1) (by simp)
  | succ n ih => rw [pow_succ, ord_mul, ih, h1]; simp

theorem valuation_of_shell {c r : kˣ} {a : ℕ} (hr : ord k r = ord k c - a) :
    valuation k (c : k) = uniformizer k ^ a * valuation k (r : k) := by
  obtain ⟨p, hp, hp'⟩ := exists_unit_pow k a
  rw [← hp, ← map_mul, ← Units.val_mul, valuation_eq_iff_ord, ord_mul]; omega

theorem IsShellReps.sum_eq {c : kˣ} {a : ℕ} {R R' : Finset kˣ} (h : IsShellReps c a R) (h' : IsShellReps c a R')
    {g : kˣ → ℂ} (hg : ∀ y r : kˣ, ord k y = ord k c - a → ord k r = ord k c - a →
      valuation k ((y : k) - r) ≤ valuation k (c : k) → g y = g r) :
    ∑ r ∈ R, g r = ∑ r ∈ R', g r := by
  choose i hi hi' using fun r hr => h'.2 r (h.1 r hr)
  refine Finset.sum_bij i (fun r hr => (hi r hr).1) (fun r₁ h₁ r₂ h₂ e => ?_) (fun r' hr' => ?_)
    (fun r hr => hg _ _ (h.1 r hr) (h'.1 _ (hi r hr).1) (hi r hr).2)
  · refine (h.2 _ (h'.1 _ (hi r₁ h₁).1)).unique ⟨h₁, ?_⟩ ⟨h₂, ?_⟩
    · rw [Valuation.map_sub_swap]; exact (hi r₁ h₁).2
    · rw [Valuation.map_sub_swap, e]; exact (hi r₂ h₂).2
  · obtain ⟨r, hr, -⟩ := h.2 r' (h'.1 r' hr')
    exact ⟨r, hr.1, (hi' r hr.1 r' ⟨hr', by rw [Valuation.map_sub_swap]; exact hr.2⟩).symm⟩


variable {ψ : AddChar k Circle} {χ : kˣ →* ℂˣ} {c : kˣ} {a : ℕ} {R R' : Finset kˣ}

theorem addChar_eq_of_sub (hψ : HasConductor ψ c) {y z : k} (h : valuation k (y - z) ≤ valuation k (c : k)) :
    ψ y = ψ z := by
  have : y = z + (y - z) := by ring
  rw [this, AddChar.map_add_eq_mul, hψ.eq_one h, mul_one]

theorem gaussTerm_eq (hψ : HasConductor ψ c) (hχ : HasExponent χ a) {x : k} (hx : valuation k x ≤ 1) (y r : kˣ)
    (hy : ord k y = ord k c - a) (hr : ord k r = ord k c - a)
    (h : valuation k ((y : k) - r) ≤ valuation k (c : k)) :
    (((χ y)⁻¹ : ℂˣ) : ℂ) * (ψ (x * y) : ℂ) = (((χ r)⁻¹ : ℂˣ) : ℂ) * (ψ (x * r) : ℂ) := by
  have h1 : ψ (x * y) = ψ (x * r) := addChar_eq_of_sub hψ (by
    rw [← mul_sub, map_mul]
    exact (mul_le_mul' hx h).trans_eq (one_mul _))
  have hr0 : 0 < valuation k (r : k) := by simp [zero_lt_iff]
  have h2 : χ (y * r⁻¹) = 1 := hχ.1 _ ⟨by
    rw [Units.val_mul, map_mul, valuation_eq_iff_ord.2 (hy.trans hr.symm), ← map_mul]; simp, by
    have : ((y * r⁻¹ : kˣ) : k) - 1 = ((y : k) - r) * (r : k)⁻¹ := by simp [sub_mul]
    rw [this, map_mul, map_inv₀, mul_inv_le_iff₀ hr0, ← valuation_of_shell hr]
    exact h⟩
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h1, h2]

theorem IsTateEps.unique {e e' : ℂ} (h : IsTateEps ψ χ e) (h' : IsTateEps ψ χ e') : e = e' := by
  obtain ⟨c, a, R, hc, ha, hR, rfl⟩ := h
  obtain ⟨c', a', R', hc', ha', hR', rfl⟩ := h'
  obtain rfl := ha.unique ha'
  have h1 : valuation k (c' : k) = valuation k (c : k) :=
    le_antisymm ((hc _).1 ((hc' _).2 le_rfl)) ((hc' _).1 ((hc _).2 le_rfl))
  rw [IsShellReps, valuation_eq_iff_ord.1 h1, h1] at hR'
  have := hR.sum_eq hR' (gaussTerm_eq hc ha (x := 1) (by simp))
  simp only [one_mul] at this
  rw [this]

end GlobalTheory.LocLanglands
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSum
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemIntegral

theorem toEAf_mem_of_finPart {D : D7} {w : AE D} (hw : finPart D w ∈ intAE D) :
    toEAf D w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have key : ∀ z ∈ intAE D, Algebra.TensorProduct.comm D.host.F (Formalism.L2.Herm.Af D.host.F) D.host.E z ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, rfl⟩ := hz
      have h1 : (1 : D.host.E) ⊗ₜ[D.host.F] a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)
      have h2 : (x : D.host.E) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)
      have h3 := mul_mem h2 h1
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one] at h3
      exact h3
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | neg x _ hx => rw [map_neg]; exact neg_mem hx
  exact key _ hw

theorem toEAf_incA (D : D7) (x : D.host.E) : toEAf D (incA D x) = eToEAf D x := rfl

theorem eToEAf_int (D : D7) (x : 𝓞 D.host.E) :
    eToEAf D (x : D.host.E) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  Subring.subset_closure (Or.inl ⟨⟨_, x, rfl⟩, rfl⟩)

theorem conj_mem_at (D : D7) (e : AE D) (PP : HeightOneSpectrum (𝓞 D.host.E)) (he : Formalism.L2.NTheta.IsIdemAt e PP)
    (hP : ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (a : D.host.E) (ha : a ∈ D.host.AA) :
    toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  set n : ℕ := Ideal.absNorm D.host.𝔟 with hn
  have hnP : (n : 𝓞 D.host.E) ∉ PP.asIdeal := by
    intro h
    obtain ⟨p, hp, hpP⟩ := GlobalTheory.HalfCompare.exists_prime_under PP
    exact hP ((hpP _).2 (((GlobalTheory.HalfCompare.prime_dvd_absNorm_halfDifferent D hp).1 ((hpP _).1 h)).mul_right _))
  have hn0 : (n : 𝓞 D.host.E) ≠ 0 := fun h => hnP (h ▸ zero_mem _)
  have hn0' : (n : D.host.E) ≠ 0 := by
    intro h
    apply hn0
    have : n = 0 := by exact_mod_cast h
    rw [this, Nat.cast_zero]
  have h1 : finPart D (e * incA D (((n : 𝓞 D.host.E) : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hnP ((he.2 _ hn0).2 h)
  have h2 := toEAf_mem_of_finPart h1
  obtain ⟨c, hc⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA.int_of_mem_b D (Ideal.absNorm_mem D.host.𝔟) ha
  have hi : IsIntegral ℤ (D.sp.cm.sig (c : D.host.E)) :=
    (show IsIntegral ℤ (c : D.host.E) from c.2).map (D.sp.cm.sig : D.host.E →+* D.host.E).toIntAlgHom
  have h3 := mul_mem h2 (eToEAf_int D ⟨_, hi⟩)
  rw [map_mul, toEAf_incA, mul_assoc, ← map_mul] at h3
  convert h3 using 3
  have hc' : (c : D.host.E) = a * n := hc
  have hcast : ((n : 𝓞 D.host.E) : D.host.E) = n := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) n
  change D.sp.cm.sig a = ((n : 𝓞 D.host.E) : D.host.E)⁻¹ * D.sp.cm.sig (c : D.host.E)
  rw [hc', hcast, map_mul, map_natCast]
  field_simp

theorem conj_mem_intAf : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rintro D e P ⟨⟨es, hes, rfl⟩, -⟩ hP a ha
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul]
  exact sum_mem fun PP hPP => conj_mem_at D _ PP (hes PP hPP) (hP PP hPP) a ha

end GlobalTheory.IdemIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjPrincipalFractionalIntegralIdempotentSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_principalFractional_integral_idempotentSum : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ a : D.host.E, a ∈ D.host.AA → toEAf D e * eToEAf D (D.sp.cm.sig a) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  first | exact @GlobalTheory.IdemIntegral.conj_mem_intAf | exact GlobalTheory.IdemIntegral.conj_mem_intAf | (intros; apply GlobalTheory.IdemIntegral.conj_mem_intAf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormIntegrality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.FactsLat

variable {D : D7}

theorem selfDual_frame_level_one_lattice_eq_standard {V : HSp D} {β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (h : IsSDFrame V β Λ 1) :
    (Λ : Set (Fin V.rank → D.host.E)) = Formalism.MainNotions.StandardLattice.L0c D V := by
  obtain ⟨c, -, -, -, h1, h2⟩ := h
  simp only [one_pow, Nat.cast_one, one_smul] at h1 h2
  exact Set.ext fun x => ⟨h2 x, h1 x⟩

theorem pi_eq_stdL (E : Type) [Field E] [NumberField E] (n : ℕ) :
    (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) = stdL E n := by
  apply le_antisymm
  · intro x hx
    rw [← Finset.univ_sum_single x]
    refine Submodule.sum_mem _ fun a _ => ?_
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hx a trivial)
    have : (Pi.single a (x a) : Fin n → E) = b • (Pi.single a 1 : Fin n → E) := by
      rw [← Pi.single_smul, ← hb, Algebra.smul_def, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩ j -
    by_cases h : j = a
    · subst h
      exact Submodule.mem_one.2 ⟨1, by simp⟩
    · simp [h]

theorem arr_injective {n : ℕ} {q : ℕ} (hq : q ≤ n) : Function.Injective (arr q : Fin n → Fin n) := by
  intro a b h
  have h' := congrArg Fin.val h
  have := a.2
  have := b.2
  unfold arr at h'
  apply Fin.ext
  split_ifs at h' <;> simp only at h' <;> omega

section Model

variable {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {p q : ℕ} (hpq : p + q = V.rank)
  (hε : ∀ τ a, M.ε τ a = decide ((a : ℕ) < p))
include hpq hε

theorem nNeg_eq (τ : D.what₂.Tau) : nNeg (M.ε τ) = q := by
  rw [nNeg_shape (by omega) (hε τ)]; omega

theorem negM_eq (τ : D.what₂.Tau) :
    negM V q = diagonal fun c => (if M.ε τ (arr (nNeg (M.ε τ)) c) = true then (1 : ℂ) else -1) := by
  unfold negM
  congr 1
  funext c
  have := c.2
  rw [nNeg_eq M hpq hε, hε, arr, sgn]
  by_cases h : (c : ℕ) < q
  · rw [dite_eq_left h, if_pos h, if_neg (by simp only [decide_eq_true_eq]; omega)]; simp
  · rw [dite_eq_right h, if_neg h, if_pos (by simp only [decide_eq_true_eq]; omega)]; simp

theorem isONeg_x0Mat : IsONeg V q (x0Mat M) := by
  intro τ
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have h1 : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h2 : (onb M τ)ᴴ * gramAt D V τ * onb M τ = Formalism.REAL.Jm (M.ε τ) := by
    rw [← M.fr_gram τ]; unfold onb
    calc _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp
  have h3 : (x0Mat M τ)ᴴ * gramAt D V τ * x0Mat M τ =
      ((onb M τ)ᴴ * gramAt D V τ * onb M τ).submatrix (arr (nNeg (M.ε τ))) (arr (nNeg (M.ε τ))) := rfl
  rw [h3, h2, negM_eq M hpq hε τ, Formalism.REAL.Jm, Matrix.submatrix_diagonal _ _ (arr_injective (nNeg_le _))]
  rfl

theorem cart_eq_cartZ : cart M = cartZ V q (x0Mat M) := by
  funext τ
  have hn : negM V q * negM V q = 1 := by
    rw [negM_eq M hpq hε τ, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext a; split_ifs <;> simp
  have h1 : (negM V q * ((x0Mat M τ)ᴴ * gramAt D V τ)) * x0Mat M τ = 1 := by
    rw [Matrix.mul_assoc, isONeg_x0Mat M hpq hε τ, hn]
  have hu : IsUnit (x0Mat M τ).det := Matrix.isUnit_det_of_left_inverse h1
  rw [cartZ, negM_eq M hpq hε τ, ← torus_x0Mat M τ fun a => if M.ε τ a = true then (1 : ℂ) else -1,
    Matrix.mul_nonsing_inv_cancel_right _ _ hu]
  rfl

end Model

theorem muVal_cast {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV; exact h

theorem latEmb_cast {V W : HSp D} (hV : V = W) {r : ℕ} (hr : V.rank = r) (hr' : W.rank = r) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin r → D.host.E))
    (h : LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι)) :
    LatEmb W (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr') ∘ₗ ι) := by
  subst hV; exact h

theorem isAA_span {k : ℕ} (L : Lt D.host.E k) : GlobalTheory.Ker.IsAA (Submodule.span (𝓞 D.host.E)
    {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ L, w = a • v}) L := by
  intro v
  rw [← Submodule.mem_toAddSubgroup]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact AddSubgroup.subset_closure hx
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul c x hx' hx =>
      clear hx'
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hx
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le _).2 (fun x hx => Submodule.subset_span hx) hv

theorem isMov_hLat (W : HSp D) (h : GA D W) :
    GlobalTheory.Ker.IsMov (GlobalTheory.Ker.fmt W h) (Bridge.hLat W 1) (Bridge.hLat W (FWT.fin W h)) := by
  intro u
  rw [GlobalTheory.MovedLat.hLat_one]
  have := Set.ext_iff.1 (GlobalTheory.MovedLat.hat_hLat W (FWT.fin W h)) u
  exact this.trans ⟨fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩, fun ⟨z, hz, e⟩ => ⟨z, hz, e.symm⟩⟩

end GlobalTheory.OneMapRef.FactsLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Twist

namespace GlobalTheory.ProperFinite

variable {X X' : Scheme.{0}}

theorem notMem_support_of_subsingleton (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens} (hV : IsAffineOpen V)
    [Subsingleton Γ(F, V)] {x : X} (hx : x ∈ V) : x ∉ support F := fun h => by
  have h' := (mem_support_iff_primeIdealOf (F := F) hV ⟨x, hx⟩).1 h
  rw [Module.support_eq_empty] at h'
  exact h'

theorem nonempty_coh_pushforward_equiv (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)] [Algebra R Γ(X', ⊤)]
    (π : X' ⟶ X) (hπ : ∀ r, π.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap R Γ(X', ⊤) r)
    (E : X'.Modules) [((Scheme.Modules.pushforward π).obj E).IsQuasicoherent] {m : ℕ} {U : Fin m → X.Opens}
    (hc : ⨆ i, U i = ⊤) (hU : ∀ s : Finset (Fin m), s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i))
    (hE : ∀ s : Finset (Fin m), s.Nonempty → ∀ q, 0 < q → Subsingleton (cohOn E (π ⁻¹ᵁ (⨅ i ∈ s, U i)) q))
    (p : ℕ) : Nonempty (coh ((Scheme.Modules.pushforward π).obj E) p ≃ₗ[R] coh E p) := by
  have hc' : π ⁻¹ᵁ ⊤ ≤ ⨆ i, π ⁻¹ᵁ U i := by rw [← Scheme.Hom.preimage_iSup, hc]
  have ha : CechAcyclicMod (π ⁻¹ᵁ ⊤) (fun i => π ⁻¹ᵁ U i) E :=
    (cechAcyclicMod_iff_of_le fun _ => le_top).2 fun s hs q hq => by
      have := hE s hs q hq
      have e : π ⁻¹ᵁ (⊤ ⊓ ⨅ i ∈ s, U i) = ⊤ ⊓ ⨅ i ∈ s, π ⁻¹ᵁ U i := preimage_cechOpen π ⊤ U s
      rwa [← top_inf_eq (⨅ i ∈ s, U i), e, top_inf_eq] at this
  exact ⟨(cechHEquivCoh R hc hU _ p).symm ≪≫ₗ
    ((HomologicalComplex.homologyFunctor _ _ p).mapIso (cechPushforwardIso ⊤ U E hπ)).toLinearEquiv ≪≫ₗ
    cechHEquivCohOn R hc' ha p⟩

theorem eventually_subsingleton_cohOn [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] {V : X.Opens} (hV : IsAffineOpen V) :
    ∀ᶠ n : ℕ in atTop, ∀ q, 0 < q → Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ V) q) := by
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  refine (hj.eventually_subsingleton_coh_twist (f := g) (fun _ => rfl) (E.restrict j)).mono fun n hn q hq => ?_
  have := hn q hq
  obtain ⟨e⟩ := nonempty_iso_of_lbIso (F := E.restrict j) (LB.isLB_pull (isLB_lbPow hL.isLB n) j)
    (isLB_lbPow hj.isLB n) (lbIso_lbPow_pull hL.isLB j n).symm
  let e' : (twist E (lbPow L n)).restrict j ≅ twist (E.restrict j) (lbPow (L.pull j) n) :=
    (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫ Twist.pullbackIso E j (isLB_lbPow hL.isLB n) ≪≫
      (twistFunctor _).mapIso ((Scheme.Modules.restrictFunctorIsoPullback j).app _).symm ≪≫ e
  exact ((cohOn.restrictEquiv ℤ (g := j) (fun r => by simp) _ (π ⁻¹ᵁ V).ι_image_top q).trans
    (cohOn.mapIso ℤ ⊤ q e')).injective.subsingleton

theorem topIso_inv_appTop (π : X' ⟶ X) (V : X.Opens) :
    V.topIso.inv ≫ (π ∣_ V).appTop = π.appLE V ((π ⁻¹ᵁ V).ι ''ᵁ ⊤) (π ⁻¹ᵁ V).ι_image_top.le := by
  rw [morphismRestrict_appTop, Scheme.Opens.topIso_inv, Scheme.Hom.app_eq_appLE]
  exact (congrArg (_ ≫ ·) (π.appLE_map _ _)).trans (π.map_appLE _ _)

theorem isFiniteQC_pushforward [IsLocallyNoetherian X] (π : X' ⟶ X) [IsProper π] {L : LB X'}
    (hL : IsAmpleLB L) (E : X'.Modules) [IsFiniteQC E] : IsFiniteQC ((Scheme.Modules.pushforward π).obj E) := by
  refine ⟨inferInstance, fun V hV => ?_⟩
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have := hL.noetherianSpace
  let j := (π ⁻¹ᵁ V).ι
  let g : (π ⁻¹ᵁ V).toScheme ⟶ Sp Γ(X, V) := π ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g := inferInstanceAs (IsProper (π ∣_ V ≫ hV.isoSpec.hom))
  letI := algebraΓOfHom g
  have hj : IsAmpleLB (L.pull j) := hL.pull_of_isImmersion j
  have hfin := hj.finite_coh (f := g) (fun _ => rfl) (E.restrict j) 0
  have hfin' := Module.Finite.equiv (cohOn.zeroEquiv Γ(X, V) (E.restrict j) ⊤)
  have hle : j ''ᵁ ⊤ ≤ π ⁻¹ᵁ V := (π ⁻¹ᵁ V).ι_image_top.le
  have ha : ∀ r, algebraMap Γ(X, V) Γ((π ⁻¹ᵁ V).toScheme, ⊤) r = π.appLE V (j ''ᵁ ⊤) hle r := fun r => by
    change (π ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(X, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, topIso_inv_appTop]
    rfl
  let ρ : Γ((Scheme.Modules.pushforward π).obj E, V) →ₗ[Γ(X, V)] sectionsOn (E.restrict j) ⊤ :=
    { toFun := fun s => (sectionsOn.toΓ (E.restrict j) ⊤).symm (E.presheaf.map (homOfLE hle).op s)
      map_add' := fun s t => (congrArg _ (map_add (E.presheaf.map (homOfLE hle).op).hom s t)).trans (map_add _ _ _)
      map_smul' := fun r s => (sectionsOn.toΓ (E.restrict j) ⊤).injective (by
        rw [sectionsOn.toΓ_smul, RingHom.id_apply, ha]
        change E.presheaf.map (homOfLE hle).op (π.app V r • (show Γ(E, π ⁻¹ᵁ V) from s)) =
          (j.appIso ⊤).inv (restrictGlobal _ ⊤ (π.appLE V (j ''ᵁ ⊤) hle r)) • E.presheaf.map (homOfLE hle).op s
        rw [Scheme.Modules.map_smul, Scheme.Opens.ι_appIso]
        exact congrArg (· • _) (res_self_ring (X := (π ⁻¹ᵁ V).toScheme) le_top _).symm) }
  have hρ : Function.Bijective ρ :=
    (sectionsOn.toΓ (E.restrict j) ⊤).symm.bijective.comp (res_bijective_of_eq E hle (π ⁻¹ᵁ V).ι_image_top)
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ).symm

theorem bijective_unit_app (π : X' ⟶ X) {U V : X.Opens} [IsIso (π ∣_ U)] (h : V ≤ U) (hV : IsAffineOpen V)
    (G : X.Modules) [G.IsQuasicoherent] :
    Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G).app V) := by
  have hi : IsIso (π ∣_ V) := by
    have h₁ : IsIso (π ∣_ U ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
    have h₂ := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict π U (U.ι ⁻¹ᵁ V))).1 h₁
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.2 h] at h₂
  have hV' : IsAffineOpen (π ⁻¹ᵁ V) := by
    have : IsAffine V := hV
    exact IsAffine.of_isIso (π ∣_ V)
  have hb : Function.Bijective (π.appLE V (π ⁻¹ᵁ V) le_rfl) := by
    have h₀ : IsIso (π ∣_ V).appTop := inferInstanceAs (IsIso ((π ∣_ V).app ⊤))
    have h₁ : IsIso (V.topIso.inv ≫ (π ∣_ V).appTop) := inferInstance
    rw [topIso_inv_appTop, ← π.appLE_map le_rfl (eqToHom (π ⁻¹ᵁ V).ι_image_top).op] at h₁
    have := @IsIso.of_isIso_comp_right _ _ _ _ _ (π.appLE V (π ⁻¹ᵁ V) le_rfl)
      (X'.presheaf.map (eqToHom (π ⁻¹ᵁ V).ι_image_top).op) inferInstance h₁
    exact ConcreteCategory.bijective_of_isIso _
  letI := appLEAlgebra π (le_refl (π ⁻¹ᵁ V))
  letI := appLEModule π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  haveI := appLE_isScalarTower π ((Scheme.Modules.pullback π).obj G) (le_refl (π ⁻¹ᵁ V))
  have hB := isBaseChange_pullbackSections π G hV' hV le_rfl
  have h₁ : Function.Bijective (pullbackSections π G (le_refl (π ⁻¹ᵁ V))) := by
    let e := (TensorProduct.lid Γ(X, V) Γ(G, V)).symm ≪≫ₗ
      (LinearEquiv.ofBijective (Algebra.linearMap Γ(X, V) Γ(X', π ⁻¹ᵁ V)) hb).rTensor Γ(G, V)
    have he : ⇑(pullbackSections π G (le_refl (π ⁻¹ᵁ V))) = hB.equiv ∘ e := funext fun m => by
      change _ = hB.equiv (algebraMap Γ(X, V) Γ(X', π ⁻¹ᵁ V) 1 ⊗ₜ m)
      rw [map_one, hB.equiv_tmul, one_smul]
    rw [he]
    exact hB.equiv.bijective.comp e.bijective
  exact (Function.Bijective.of_comp_iff' (res_bijective_of_eq ((Scheme.Modules.pullback π).obj G)
    (le_refl (π ⁻¹ᵁ V)) rfl) _).1 h₁

def VanishesSomewhere (E : X.Modules) : Prop :=
  ∃ W : X.Opens, (W : Set X).Nonempty ∧ ∀ V ≤ W, IsAffineOpen V → Subsingleton Γ(E, V)

theorem finite_coh_of_bijective [IsLocallyNoetherian X] (R : Type) [CommRing R] [IsNoetherianRing R]
    [Algebra R Γ(X, ⊤)]
    (ih : ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    {F G : X.Modules} [IsFiniteQC F] [IsFiniteQC G] (φ : F ⟶ G) {W : X.Opens} (hW : (W : Set X).Nonempty)
    (hφ : ∀ V ≤ W, IsAffineOpen V → Function.Bijective (φ.app V)) (hG : ∀ p, Module.Finite R (coh G p)) :
    ∀ p, Module.Finite R (coh F p) := by
  let ψ : F ⟶ kernel (cokernel.π φ) := Abelian.factorThruImage φ
  have hψ : ψ ≫ kernel.ι _ = φ := Abelian.image.fac φ
  have : Epi ψ := inferInstanceAs (Epi (Abelian.factorThruImage φ))
  have h₂ : (ShortComplex.mk (kernel.ι (cokernel.π φ)) (cokernel.π φ) (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have h₁ : (ShortComplex.mk (kernel.ι ψ) ψ (kernel.condition _)).ShortExact :=
    { exact := ShortComplex.exact_kernel _ }
  have hC := ih (cokernel φ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => ?_
    obtain ⟨g, rfl⟩ := app_surjective_of_epi_of_isAffineOpen (cokernel.π φ) ha c
    obtain ⟨f, rfl⟩ := (hφ V hV ha).2 g
    change (φ ≫ cokernel.π φ).app V f = 0
    rw [cokernel.condition]
    rfl⟩
  have hK := ih (kernel ψ) inferInstance ⟨W, hW, fun V hV ha => by
    refine subsingleton_of_forall_eq 0 fun c => injective_kernel_ι_app ψ V ((hφ V hV ha).1 ?_)
    change (kernel.ι ψ ≫ φ).app V c = (kernel.ι ψ ≫ φ).app V 0
    rw [show kernel.ι ψ ≫ φ = 0 from (congrArg (_ ≫ ·) hψ.symm).trans (by rw [kernel.condition_assoc, zero_comp])]
    rfl⟩
  exact cohOn.forall_finite₂ R h₁ ⊤ hK (cohOn.forall_finite₁ R h₂ ⊤ hG hC)

theorem finite_coh_of_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (π : X' ⟶ X) (hP : IsProjOver (π ≫ f)) {U : X.Opens} (hU : (U : Set X).Nonempty) [IsIso (π ∣_ U)]
    (ih : letI := algebraΓOfHom f
      ∀ E : X.Modules, IsFiniteQC E → VanishesSomewhere E → ∀ p, Module.Finite R (coh E p))
    (G : X.Modules) [IsFiniteQC G] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh G p) := by
  letI := algebraΓOfHom f
  letI := algebraΓOfHom (π ≫ f)
  obtain ⟨_, L, hL⟩ := isProper_and_exists_isAmpleLB_of_isProjOver hP
  have : IsProper π := .of_comp π f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨m, D, hD, hc⟩ := exists_fin_affine_cover (X := X) (V := ⊤) isCompact_univ
  have hD' := isAffineOpen_finset_biInf hD
  let E := (Scheme.Modules.pullback π).obj G
  obtain ⟨u, hu⟩ := hU
  let σ : U.toScheme ⟶ X' := inv (π ∣_ U) ≫ (π ⁻¹ᵁ U).ι
  obtain ⟨d, hd, s, hs, -⟩ := hL.exists_affine (σ ⟨u, hu⟩)
  have H : ∀ᶠ n : ℕ in atTop, ∀ I : Finset (Fin m), I.Nonempty → ∀ q, 0 < q →
      Subsingleton (cohOn (twist E (lbPow L n)) (π ⁻¹ᵁ (⨅ i ∈ I, D i)) q) :=
    eventually_all.2 fun I => eventually_all.2 fun hI => eventually_subsingleton_cohOn π hL E (hD' I hI)
  obtain ⟨n, hn⟩ := eventually_atTop.1 H
  have hN := isLB_lbPow hL.isLB (d * (n + 1))
  let t : (lbPow L (d * (n + 1))).Sec := secPow s (n + 1)
  have ht : Out.nonzeroLocus t = Out.nonzeroLocus s := nonzeroLocus_secPow s n.succ_pos
  have := isFiniteQC_twist (F := E) hN
  have := isFiniteQC_pushforward π hL (twist E (lbPow L (d * (n + 1))))
  refine finite_coh_of_bijective R ih ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app G ≫
    (Scheme.Modules.pushforward π).map (secHom E t)) (W := U.ι ''ᵁ (σ ⁻¹ᵁ Out.nonzeroLocus s))
    ⟨u, ⟨u, hu⟩, hs, rfl⟩ (fun V hV ha => ?_) fun p => ?_
  · have h₁ : V ≤ U := hV.trans (U.ι_image_le _)
    have h₂ : π ⁻¹ᵁ V ≤ Out.nonzeroLocus t := fun x hx => by
      obtain ⟨y, hy, e⟩ := hV hx
      have e₁ : (π ∣_ U) ⟨x, h₁ hx⟩ = y := Subtype.ext ((morphismRestrict_base_coe π U _).trans e.symm)
      have e₂ : σ y = x := by
        rw [← e₁]
        exact congrArg (fun q => q (⟨x, h₁ hx⟩ : (π ⁻¹ᵁ U).toScheme)) (IsIso.hom_inv_id_assoc (π ∣_ U) (π ⁻¹ᵁ U).ι)
      rw [ht, ← e₂]
      exact hy
    exact (bijective_secHom_app hN t h₂).comp (bijective_unit_app π h₁ ha G)
  · obtain ⟨e⟩ := nonempty_coh_pushforward_equiv R π (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) hc hD'
      (hn _ (le_trans n.le_succ (Nat.le_mul_of_pos_left _ hd))) p
    have := hL.finite_coh (f := π ≫ f) (fun _ => rfl) (twist E (lbPow L (d * (n + 1)))) p
    exact Module.Finite.equiv e.symm

theorem support_pushforward_ssubset (ι : X' ⟶ X) [IsClosedImmersion ι] (E : X'.Modules) [E.IsQuasicoherent]
    (h : VanishesSomewhere E) : support ((Scheme.Modules.pushforward ι).obj E) ⊂ Set.range ι := by
  obtain ⟨W, ⟨z, hz⟩, hW⟩ := h
  refine ⟨fun x hx => by_contra fun hx' => ?_, fun hle => ?_⟩
  · obtain ⟨V, hV, hxV, hle⟩ := exists_affine_mem_le
      (U := ⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩) x hx'
    have e : ι ⁻¹ᵁ V = ⊥ := le_bot_iff.1 fun y hy => (hle hy ⟨y, rfl⟩).elim
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (e ▸ bot_le) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV hx
  · obtain ⟨O, hO, e⟩ := ι.isClosedEmbedding.isInducing.isOpen_iff.1 W.isOpen
    obtain ⟨V, hV, hxV, hle'⟩ := exists_affine_mem_le (U := ⟨O, hO⟩) (ι z) (e.ge hz)
    have : Subsingleton Γ((Scheme.Modules.pushforward ι).obj E, V) := by
      change Subsingleton Γ(E, ι ⁻¹ᵁ V)
      exact hW _ (fun y hy => e.le (hle' hy)) (hV.preimage ι)
    exact notMem_support_of_subsingleton _ hV hxV (hle ⟨z, rfl⟩)

theorem finite_coh_of_forall_modification {R : Type} [CommRing R] [IsNoetherianRing R] (f : X ⟶ Sp R) [IsProper f]
    (h : ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι : Z ⟶ X) [IsClosedImmersion ι], ∃ (Z' : Scheme.{0}) (π : Z' ⟶ Z)
      (U : Z.Opens), IsProjOver (π ≫ ι ≫ f) ∧ (U : Set Z).Nonempty ∧ IsIso (π ∣_ U))
    (F : X.Modules) [IsFiniteQC F] : letI := algebraΓOfHom f; ∀ p, Module.Finite R (coh F p) := by
  letI := algebraΓOfHom f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := {}
  refine devissage X (fun F => ∀ p, Module.Finite R (coh F p)) (fun F hF p => ?_)
    (fun S hS _ _ h₁ h₃ => cohOn.forall_finite₂ R hS ⊤ h₁ h₃) (fun Z hZ ih G hG p => ?_) F inferInstance
  · have := cohOn.subsingleton_of_isZero hF ⊤ p
    infer_instance
  · have := isIntegral_red hZ
    letI := algebraΓOfHom (redι Z ≫ f)
    obtain ⟨Z', π, U, hP, hU, _⟩ := h _ (redι Z)
    have := finite_coh_of_modification (redι Z ≫ f) π hP hU (fun E hE hv q => by
      have := ih ((Scheme.Modules.pushforward (redι Z)).obj E)
        ⟨inferInstance, fun V hV => finite_sections_pushforward _ _ hV (hF := finite_sections E (hV.preimage _))⟩
        (range_redι Z ▸ support_pushforward_ssubset (redι Z) E hv) q
      exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) E q)) G p
    exact Module.Finite.equiv (coh.pushforwardEquiv R (g := redι Z) (fun _ => rfl) G p).symm

end GlobalTheory.ProperFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsSpanOfOnto
noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.OneMapTuples

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Data

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
  (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))

def XiConst (ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) (c0 : ℂ) : Prop :=
  ∀ t, GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC O.c') (O.dδ t) (O.U₂ t) (O.dict₂ t) ι x₀ (O.xi t) c0

abbrev IsCls (t : Tp) (x : O.Cl' t → VsV D i O.c'.F) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev rdQ (z : G) (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : AutQ (Wc D i) → ℂ :=
  jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu (actLev O.c' O.lev2 z f)

def ClsEx : Prop :=
  ∀ t x, O.Plc t x →
    ∃ f ∈ cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank, IsCls O t x f ∧
      ∀ f' ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f' → f' = f

def PtIdent (lam : AutQ (Wc D i) → ℂ) (z : G) (c0 : ℂ) : Prop :=
  ∀ t, ∃ ze : ℂ, ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x, O.Plc t x →
    ∀ f ∈ sec (C.Q.Xo ((i : ℕ) + 1)) O.c' (wtA κ) (Vc D i).rank, IsCls O t x f →
      ∀ q, c0 * O.thAd t x q = ze * lam q * rdQ O z f q

end Data

abbrev liftQ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) (t : T0) (x : A.fam.amb.FL i t) : AutQ (Wc D i) → ℂ :=
  onQ (Wc D i) (R.thF i t (jVx R i t x) v)

def LiftsSpan {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (v : (R.MW i (sg0 D A)).Vec) : Prop :=
  ∀ (t : T0) (x : A.fam.amb.FL i t), liftQ R i v t x ∈ Submodule.span ℂ (Set.range (liftQ R i v A.μ0))

def PinsExist (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

end GlobalTheory.OneMapTuples
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelAction

theorem conj_mulVec_mem {R : Type} [CommRing R] {n : ℕ} (S : Subring R) (β : GL (Fin n) R) (y : GL (Fin n) S)
    (z : Fin n → R) (hz : ∀ j, ((β⁻¹).1 *ᵥ z) j ∈ S) (i : Fin n) :
    ((β⁻¹).1 *ᵥ ((β * Formalism.UG.bc S.subtype y * β⁻¹).1 *ᵥ z)) i ∈ S := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  generalize (β⁻¹).1 *ᵥ z = w at hz
  exact Subring.sum_mem S (t := Finset.univ) (f := fun j => (y.1 i j : R) * w j) fun j _ => mul_mem (y.1 i j).2 (hz j)

variable {D : D7}

theorem finCong_of_mem_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {k : GA D V}
    (hk : Lev.finE V k ∈ St β) : GlobalTheory.Member.FinCong V 1 k := by
  have hl : latHat V = GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    rw [GlobalTheory.PrincInLevel.eq_latC hβ]; exact (GlobalTheory.Member.latHat_eq_hat_and_gram D V).1
  obtain ⟨c, hfr, -⟩ := hβ
  obtain ⟨y, hy⟩ := hk
  have hy' : β * intGL D.host.F D.host.E V.rank y * β⁻¹ = Formalism.UG.bc (Lev.swapAE D) (finHom V k) := hy
  intro z hz
  refine ⟨(finHom V k).1 *ᵥ z - z, sub_mem ?_ hz, (one_nsmul _).symm⟩
  rw [hl] at hz ⊢
  have h2 := (hfr _).1 (GlobalTheory.PrincInLevel.swap_mem_hatL Λ z hz)
  have h3 : (Formalism.UG.bc (Lev.swapAE D) (finHom V k)).1 *ᵥ
      (fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E (z i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    rw [← hy']
    exact (hfr _).2 (conj_mulVec_mem _ β y _ h2)
  have h4 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h3
  convert h4 using 1
  funext i
  rw [AlgEquiv.eq_symm_apply]
  exact RingHom.map_mulVec (Lev.swapAE D) (finHom V k).1 z i

theorem exists_endo {V : HSp D} {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (hι : LatEmb V ι) {M : ℕ} (hM : 0 < M) {k : GA D V}
    (hk : GlobalTheory.Member.FinCong V 1 k) : ∃ f : La →ₗ[𝓞 D.host.E] La, ∀ a, ∃ w ∈ latGHat V 1,
      finVec V (ι (f a)) - (finHom V k).1.mulVec (finVec V (ι a)) = M • w := by
  have hh := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hk
  have hL := GlobalTheory.Member.LatMove.lat_eq_of_hat_eq V hh
  obtain ⟨h1, h2, -, -, h5, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V 1
  obtain ⟨-, -, h3, -⟩ := GlobalTheory.Member.latG_lattice_and_completion D V k
  rw [hL] at h3
  obtain ⟨f, hf, -⟩ := GlobalTheory.AdLat.exists_linear_approx_tower D.host.F D.host.E V.rank (latG V 1) (finHom V k)
    (latG V 1) h1 h2 h3
  let e : La ≃ₗ[𝓞 D.host.E] latG V 1 := (LinearEquiv.ofInjective ι hι.1).trans (LinearEquiv.ofEq _ _ hι.2)
  have he : ∀ a, (e a : Fin V.rank → D.host.E) = ι a := fun a => rfl
  refine ⟨e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap, fun a => ?_⟩
  obtain ⟨w, hw, ew⟩ := hf M hM (e a)
  refine ⟨(finHom V k).1 *ᵥ w, ?_, ?_⟩
  · rw [← hh]
    exact (GlobalTheory.Member.LatMove.mem_hat_iff V k _).2 ⟨w, h5 ▸ hw, rfl⟩
  · have e1 : ι ((e.symm.toLinearMap ∘ₗ f M ∘ₗ e.toLinearMap) a) = (f M (e a) : Fin V.rank → D.host.E) := by
      rw [← he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    rw [e1]
    have e2 : finVec V (f M (e a) : Fin V.rank → D.host.E) = (finHom V k).1 *ᵥ (finVec V (ι a) + M • w) := ew
    rw [e2, Matrix.mulVec_add, add_sub_cancel_left]
    exact map_nsmul (finHom V k).1.mulVecLin M w

theorem not_isConjPl {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H)
    {PP PP' : Pl D.host.E} (h : l.Mb ≤ PP.asIdeal) (h' : l.Mb ≤ PP'.asIdeal) : ¬ Lev.IsConjPl PP PP' := by
  intro hc
  apply PP'.isPrime.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h' (Ideal.map_le_iff_le_comap.2 fun c hc' => ?_)
  obtain ⟨c', h1, h2⟩ := hc c (h hc')
  have e : H.bar c = c' := RingOfIntegers.ext ((H.bar_eq c).trans h2.symm)
  change H.bar c ∈ PP'.asIdeal
  rwa [e]

theorem latEmb_iotaW (T : CoreJ D) (hT : LawsJ T) (i : Fin D.R.m) : LatEmb (Wc D i) (iotaW T i) := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  obtain ⟨hr, g, e, F, ik, φ, th, h, -⟩ := hT.adPin _ hj _ T.toCore.good_σ₀
  have hV := hT.spaceW _ hj _ T.toCore.good_σ₀
  have key : ∀ (V : HSp D) (hr : V.rank = D.R.r), V = Wc D i →
      LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ T.iota ((i : ℕ) + 1)) →
      LatEmb (Wc D i) (iotaW T i) := by
    rintro V hr rfl h
    exact h
  exact key _ hr hV h

theorem exists_levIs : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR ⟨tie⟩ hpb i
  have hT := tie.laws
  have hβ := hR.lev.βW i
  have hle : ∀ PP ∈ R.Pg, T.Q.l.Mb ≤ PP.asIdeal := by
    intro PP hP
    obtain ⟨k, hk⟩ := (hR.lev.Pg PP).1 hP
    rw [hT.half.2]
    refine (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ k))).trans ?_
    rw [hpb, ← show PP.under (𝓞 D.host.K) = R.C.P.pb k from hk]
    exact Ideal.map_comap_le
  have hlift : Lev.LiftsExist (Wc D i) (R.βW i) (R.datWp i R.triv) := by
    obtain ⟨c, hc⟩ := hβ
    refine GlobalTheory.T.parahoricLevel_liftsExist _ _ _ _ _ hc (fun PP h PP' h' => ?_) (Finset.disjoint_empty_right _)
    rcases h' with h' | h'
    · exact not_isConjPl T.Q.l (hle PP h) (hle PP' h')
    · exact absurd h' (Finset.notMem_empty _)
  have hM : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  choose k hk using fun g => hlift (R.eG g)
  choose f hf using fun g => exists_endo (iotaW T i) (latEmb_iotaW T hT i) hM
    (finCong_of_mem_St hβ (parLev_St (hk g).2.1))
  exact ⟨f, fun g => ⟨k g, hk g, fun a _ => hf g a⟩⟩

end GlobalTheory.LevelAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndexStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_at_each_index : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → ∀ i : Fin D.R.m, ∃ lev, LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) lev := by
  first | exact @GlobalTheory.LevelAction.exists_levIs | exact GlobalTheory.LevelAction.exists_levIs | (intros; apply GlobalTheory.LevelAction.exists_levIs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoSmulZeroOfCompact
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRepsOpen

open Filter Topology

theorem tendsto_smul_zero_of_compact {R M : Type} [Zero R] [Zero M] [SMulWithZero R M] [TopologicalSpace R]
    [TopologicalSpace M] [ContinuousSMul R M] {a : ℕ → R} (ha : Tendsto a atTop (𝓝 0)) {C : Set M} (hC : IsCompact C)
    {y : ℕ → M} (hy : ∀ n, y n ∈ C) : Tendsto (fun n => a n • y n) atTop (𝓝 0) := by
  intro U hU
  have h : ∀ᶠ r in 𝓝 (0 : R), ∀ z ∈ C, r • z ∈ U := by
    refine hC.eventually_forall_of_forall_eventually fun z _ => ?_
    refine (continuous_smul (M := R) (X := M)).continuousAt.preimage_mem_nhds ?_
    simpa using hU
  exact (ha.eventually h).mono fun n hn => hn _ (hy n)

theorem tendsto_one_of_cong (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) (A : ℕ → Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E))
    (hA : ∀ n : ℕ, ∀ z ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)), ∃ y ∈ Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)),
      A n *ᵥ z - z = n.factorial • y) : Tendsto A atTop (𝓝 1) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ⟨rfl⟩
  have : ContinuousSMul (GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af F) _
  obtain ⟨C, hC, hLC⟩ := GlobalTheory.StabCompact.exists_compact_latHat F E L hL
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  obtain ⟨d, hd, hdL⟩ := GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  have h1 : (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hz : (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) ∈
      Formalism.MainNotions.StandardLattice.latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL, rfl⟩
  choose y hy e using fun n => hA n _ hz
  have ht := tendsto_smul_zero_of_compact (R := GlobalTheoryTheory.GenusMassVolumes.Af F) (GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele F) hC
    fun n => hLC _ (hy n)
  have ht' := ((tendsto_pi_nhds.1 ht i).mul_const ((1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] ((d : E)⁻¹))).add_const
    ((1 : Matrix (Fin M) (Fin M) (GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) i j)
  rw [Pi.zero_apply, zero_mul, zero_add] at ht'
  refine ht'.congr fun n => ?_
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have e' : (A n - 1) *ᵥ (fun k => (1 : GlobalTheoryTheory.GenusMassVolumes.Af F) ⊗ₜ[F] (d • (Pi.single j 1 : Fin M → E)) k) = n.factorial • y n := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, e]
  rw [Nat.cast_smul_eq_nsmul, ← e', ← eq_sub_iff_add_eq, ← Matrix.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem exists_finCong_le (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (hJ : IsOpen (J : Set (Bridge.Gf V))) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → fin V k ∈ J := by
  by_contra hc
  have hc' : ∀ n : ℕ, ∃ k : GA D V, GlobalTheory.Member.FinCong V n.factorial k ∧ fin V k ∉ J := fun n => by
    by_contra h
    exact hc ⟨n.factorial, n.factorial_pos, fun k hk => by_contra fun h' => h ⟨k, hk, h'⟩⟩
  choose k hk hkJ using hc'
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have key : ∀ u : ℕ → GA D V, (∀ n : ℕ, GlobalTheory.Member.FinCong V n.factorial (u n)) →
      Tendsto (fun n => (finHom V (u n)).1) atTop (𝓝 1) := fun u hu => by
    refine tendsto_one_of_cong D.host.F D.host.E _ h3 h4 _ fun n => ?_
    have := hu n
    unfold GlobalTheory.Member.FinCong at this
    rw [h1] at this
    exact this
  have ht : Tendsto (fun n => fin V (k n)) atTop (𝓝 1) := by
    rw [tendsto_subtype_rng, Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine (key k hk).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
    have := key (fun n => (k n)⁻¹) fun n => GlobalTheory.Member.PrincLevel.finCong_inv (hk n)
    simp only [map_inv] at this
    exact this
  obtain ⟨n, hn⟩ := (ht.eventually (hJ.mem_nhds J.one_mem)).exists
  exact hkJ n hn

theorem exists_rep_splitOffBad : ∀ (D : D7) (V : HSp D) (J : Subgroup (Bridge.Gf V)) (bad : ℕ), bad ≠ 0 → IsOpen (J : Set (Bridge.Gf V)) → ∀ x : Bridge.Gf V, ∃ (γ : GQ V) (h : GA D V) (k : J), SplitOffBad V bad h ∧ x = Bridge.ratF V γ * fin V h * (k : Bridge.Gf V) := by
  intro D V J bad hb hJ x
  obtain ⟨N, hN, hK⟩ := exists_finCong_le D V J hJ
  obtain ⟨h, ⟨hh, hs⟩, γ, k, e⟩ :=
    GlobalTheory.SplitReps.exists_split_rep V hN (fun k _ hk => hK k hk) (Nat.pos_of_ne_zero hb) x
  exact ⟨γ, h, k, GlobalTheory.SplitReps.splitOffBad_of_suppSplit V bad h hh hs, e⟩

end GlobalTheory.SplitRepsOpen
end
