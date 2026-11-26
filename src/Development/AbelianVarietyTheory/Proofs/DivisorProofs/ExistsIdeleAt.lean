module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleAt
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

theorem exists_factor {m : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ (p : ℕ) (U : Matrix (Fin m) (Fin p) ℂ) (V : Matrix (Fin p) (Fin m) ℂ), U * V = P ∧ V * U = 1 := by
  let L := Matrix.toLin' P
  let b := Module.finBasis ℂ (LinearMap.range L)
  let e := Pi.basisFun ℂ (Fin m)
  refine ⟨_, LinearMap.toMatrix b e (LinearMap.range L).subtype, LinearMap.toMatrix e b L.rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp, LinearMap.subtype_comp_codRestrict, LinearMap.toMatrix_eq_toMatrix']
    exact LinearMap.toMatrix'_toLin' P
  · rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_id b]
    congr 1
    ext ⟨_, y, rfl⟩ : 1
    apply Subtype.ext
    show L (L y) = L y
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP]

theorem det_idem_kron {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℂ) (hP : P * P = P) :
    ∃ p : ℕ, P.trace = p ∧ ∀ a : Matrix (Fin n) (Fin n) ℂ,
      (P ⊗ₖ a + (1 - P) ⊗ₖ (1 : Matrix (Fin n) (Fin n) ℂ)).det = a.det ^ p := _root_.GlobalTheory.OneMapRef.RealMove.det_idem_kron (m := m) (n := n) P hP

theorem detPlus_one {m n : ℕ} (s : Matrix (Fin m) (Fin m) ℂ) (hs : s * s = 1) :
    ∃ p : ℕ, s.trace = 2 * p - m ∧ ∀ (a : Matrix (Fin n) (Fin n) ℂ) (b : Matrix (Fin m) (Fin m) ℂ), s * b = b * s →
      GlobalTheory.WeilParts.detPlus 1 s a b = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det ^ n * a.det ^ p ∧
      b.det = ((1 / 2 : ℂ) • (1 + s) * b + (1 / 2 : ℂ) • (1 - s)).det *
        ((1 / 2 : ℂ) • (1 - s) * b + (1 / 2 : ℂ) • (1 + s)).det := _root_.GlobalTheory.OneMapRef.RealMove.detPlus_one (m := m) (n := n) s hs

variable {D : D7}

theorem hasInfExp_twist {χ η : (AE D)ˣ →* Circle} {τ : D.what₂.Tau} {a : ℚ} (hχ : HasInfExp D χ τ a)
    (hη : HasInfExp D η τ (1 / 2)) (k : ℕ) : HasInfExp D (χ * (η ^ k)⁻¹) τ (a - k / 2) := _root_.GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (χ := χ) (η := η) (τ := τ) (a := a) hχ hη k

theorem adele_ext {θ : InfFam D} (hθ : IsInfFam θ) {x y : AE D} (h1 : finPart D x = finPart D y)
    (h2 : ∀ τ, θ τ (infPart D x) = θ τ (infPart D y)) : x = y := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  rw [← sub_eq_zero]
  exact hσ.ext _ (by rw [RingHom.map_sub, h1, sub_self]) fun τ => by
    rw [RingHom.map_sub, RingHom.map_sub, h2, sub_self]


open Classical in
theorem exists_idele_at {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) (w : ℂ) (hw : w ≠ 0) :
    ∃ x : (AE D)ˣ, finPart D (x : AE D) = 1 ∧ ∀ τ', θ τ' (infPart D (x : AE D)) = if τ' = τ then w else 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have key : ∀ w : ℂ, ∃ x : AE D, finPart D x = 1 ∧ ∀ τ', θ τ' (infPart D x) = if τ' = τ then w else 1 := fun w =>
    ⟨1 + σ fun τ' => (if τ' = τ then w else 1) - 1, by rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero], fun τ' => by
      rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]; ring⟩
  obtain ⟨x, hx1, hx2⟩ := key w
  obtain ⟨y, hy1, hy2⟩ := key w⁻¹
  have hxy : x * y = 1 := adele_ext hθ (by rw [RingHom.map_mul, hx1, hy1, RingHom.map_one, one_mul]) fun τ' => by
    rw [RingHom.map_mul, RingHom.map_mul, hx2, hy2, RingHom.map_one, RingHom.map_one]
    split_ifs
    · exact mul_inv_cancel₀ hw
    · exact one_mul 1
  have hyx : y * x = 1 := (mul_comm y x).trans hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_, ?_⟩
  · rw [Units.val_mk]; exact hx1
  · rw [Units.val_mk]; exact hx2

theorem det_compAt (θ : InfFam D) (τ : D.what₂.Tau) {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) :
    (compAt θ τ M).det = θ τ (infPart D M.det) :=
  (RingHom.map_det ((θ τ).comp (infPart D)) M).symm

theorem finPart_cA (z : AE D) (hz : finPart D z = 1) : finPart D (cA D z) = 1 := by
  have key : ∀ z : AE D, finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul a x => rfl
  rw [key, hz, map_one]

theorem exists_root {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (hV : ∀ τ, (gramAt D V τ).det ≠ 0)
    (g : GA D V) (hg : g ∈ GinfC V) :
    ∃ x, IsDetRoot V g x ∧ ∀ (ν : (AE D)ˣ →* Circle) (c : D.what₂.Tau → ℤ), (∀ τ, HasInfExp D ν τ (c τ)) →
      ((ν x : Circle) : ℂ) = ∏ τ, (compAt θ τ (Formalism.L2.Theta.mt V g)).det ^ c τ := _root_.GlobalTheory.OneMapRef.RealMove.exists_root (θ := θ) hθ V hV g hg

end GlobalTheory.VacuumCharacter

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
open NumberField IsDedekindDomain

noncomputable section
open scoped Classical

namespace GlobalTheory.WeilM

variable (F : Type) [Field F] [NumberField F]

theorem thetaSum_pureA_bound {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
    ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖thetaSum F (pureA F f g)‖ ≤ C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := discreteTopology_denomLattice F κ hN
  have hw := ZLattice.summable_norm_pow_inv (denomLattice F κ N) (Module.finrank ℤ (denomLattice F κ N) + 1)
    (Nat.lt_succ_self _)
  set k := Module.finrank ℤ (denomLattice F κ N) + 1 with hkdef
  set W := ∑' z : denomLattice F κ N, ‖z‖⁻¹ ^ k with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun _ => by positivity
  refine ⟨{(0, 0), (k, 0)}, max B 0 * (1 + W), mul_nonneg (le_max_right _ _) (by linarith), fun f => ?_⟩
  set M := (({(0, 0), (k, 0)} : Finset (ℕ × ℕ)).sup
    (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f with hMdef
  have h00 : ∀ x, ‖f x‖ ≤ M := fun x => (SchwartzMap.norm_le_seminorm ℂ f x).trans
    (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (0, 0)) (by simp))
  have hk0 : ∀ x, ‖x‖ ^ k * ‖f x‖ ≤ M := fun x => by
    have := SchwartzMap.le_seminorm ℂ k 0 f x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)
      (i := (k, 0)) (by simp))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (h00 0)
  have hpt : ∀ z : denomLattice F κ N, ‖f z‖ ≤ (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M := fun z => by
    by_cases hz : z = 0
    · subst hz; simp only [if_true]
      have := h00 0
      have h2 : 0 ≤ ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M := by positivity
      simpa using (show ‖f 0‖ ≤ M + ‖(0 : denomLattice F κ N)‖⁻¹ ^ k * M by linarith)
    · rw [if_neg hz, zero_add]
      have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ (pow_pos hz0 _), mul_comm]
      exact hk0 z
  have hs1 : HasSum (fun z : denomLattice F κ N => if z = 0 then M else 0) M := by
    convert hasSum_ite_eq (0 : denomLattice F κ N) M
  have hsumL : Summable fun z : denomLattice F κ N => (if z = 0 then M else 0) + ‖z‖⁻¹ ^ k * M :=
    hs1.summable.add (hw.mul_right M)
  have hfL : Summable fun z : denomLattice F κ N => ‖f z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt hsumL
  have hLbound : ∑' z : denomLattice F κ N, ‖f z‖ ≤ (1 + W) * M := by
    refine (hfL.tsum_le_tsum hpt hsumL).trans (le_of_eq ?_)
    rw [hs1.summable.tsum_add (hw.mul_right M), hs1.tsum_eq, tsum_mul_right]
    ring

  have hmem : pureA F f g ∈ schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  have hsupp : Function.support (fun ξ : κ → F => ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖)
      ⊆ S := by
    intro ξ hξ
    rw [Function.mem_support, norm_ne_zero_iff, pureA_algebraMap] at hξ
    have h0 := right_ne_zero_of_mul hξ
    show ∀ i, _
    intro i
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
    mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hterm : ∀ ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ ≤
      max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := fun ξ => by
    rw [pureA_algebraMap, norm_mul, mul_comm, Function.comp_apply]
    exact mul_le_mul (le_max_of_le_left (hB _)) le_rfl (norm_nonneg _) (le_max_right _ _)
  have hsumS : Summable ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) := hfL.comp_injective hj
  calc ‖thetaSum F (pureA F f g)‖
      ≤ ∑' ξ : κ → F, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))‖ :=
        norm_tsum_le_tsum_norm (summable_norm_of_mem_schA F hmem)
    _ = ∑' ξ : S, ‖pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ.1 i))‖ :=
        (tsum_subtype_eq_of_support_subset hsupp).symm
    _ ≤ ∑' ξ : S, max B 0 * ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ :=
        ((summable_norm_of_mem_schA F hmem).subtype (fun x => x ∈ S)).tsum_le_tsum hterm (hsumS.mul_left _)
    _ = max B 0 * ∑' ξ : S, ((fun z : denomLattice F κ N => ‖f z‖) ∘ j) ξ := tsum_mul_left
    _ ≤ max B 0 * ∑' z : denomLattice F κ N, ‖f z‖ :=
        mul_le_mul_of_nonneg_left (tsum_comp_le_tsum_of_inj hfL (fun _ => norm_nonneg _) hj) (le_max_right _ _)
    _ ≤ max B 0 * ((1 + W) * M) := mul_le_mul_of_nonneg_left hLbound (le_max_right _ _)
    _ = max B 0 * (1 + W) * M := by ring

theorem exists_adm_eq_thetaSum_of_locallyCompact (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)]
    (κ : Type) [Fintype κ] : ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm κ ∧
      ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := by
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (thetaLin F κ)
  have hl' : ∀ Φ ∈ schA F κ, l Φ = thetaSum F Φ := fun Φ h => by
    have := LinearMap.congr_fun hl ⟨Φ, h⟩
    simpa using this
  refine ⟨l, fun g hg => ?_, hl'⟩
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, pureA F f g ∈ schA F κ :=
    fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hadd : ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      pureA F (f + f') g = pureA F f g + pureA F f' g := fun f f' => by
    funext x; simp [pureA, add_mul]
  have hsmul : ∀ (a : ℂ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      pureA F (a • f) g = a • pureA F f g := fun a f => by
    funext x; simp [pureA, mul_assoc]
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ :=
    SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ) (fun f => thetaSum F (pureA F f g))
      (fun f f' => by rw [hadd]; exact thetaSum_add F (hmem f) (hmem f'))
      (fun a f => by rw [hsmul, thetaSum_smul]; rfl) (thetaSum_pureA_bound F hg)
  exact ⟨T, fun f => hl' _ (hmem f)⟩

end GlobalTheory.WeilM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSumStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_admissibleForm_adelicThetaSum : ∀ (F : Type) [Field F] [NumberField F] [LocallyCompactSpace (AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ], ∃ l : ((κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ ∧ ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  first | exact @GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | exact GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact | (intros; apply GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfMemCell
noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.JSW.MirPatch

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : Set (GA E a) :=
  {p | ∃ u ∈ NA (E := E) (a := a), ∃ k ∈ K, ∃ y : GL (Fin a) (Cinf E), p = u * q * finGL E a k * infGL E a y}

theorem self_mem_cell (K : Subgroup (GL (Fin a) (Af E))) (q : GA E a) : q ∈ cell K q :=
  ⟨1, ⟨fun i j h => by simp [Matrix.one_apply_ne (Fin.ne_of_gt h)], fun i => by simp⟩, 1, K.one_mem, 1, by simp⟩

end GlobalTheory.JSW.MirPatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurPolar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem exists_of_diag (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M)
    {a b s t : ℂ} (ha : IsMultIP M μ 𝓕 T T a) (hb : IsMultIP M μ 𝓕 T' T' b)
    (hs : IsMultIP M μ 𝓕 (T + T') (T + T') s)
    (ht : IsMultIP M μ 𝓕 (T + Complex.I • T') (T + Complex.I • T') t) :
    IsMultIP M μ 𝓕 T T' ((1 / 2) * ((s - a - b) - Complex.I * (t - a - b))) := by
  intro v v'
  obtain ⟨ia, ea⟩ := ha v v'
  obtain ⟨ib, eb⟩ := hb v v'
  obtain ⟨is, es⟩ := hs v v'
  obtain ⟨it, et⟩ := ht v v'
  have e : (fun g => star (T v g) * T' v' g) =
      fun g => (1 / 2 : ℂ) * ((star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
        - star (T v g) * T v' g - star (T' v g) * T' v' g)) := by
    funext g
    show _ = (1 / 2 : ℂ) * ((star (T v g + T' v g) * (T v' g + T' v' g) - star (T v g) * T v' g
        - star (T' v g) * T' v' g) - Complex.I * (star (T v g + Complex.I * T' v g) * (T v' g + Complex.I * T' v' g)
        - star (T v g) * T v' g - star (T' v g) * T' v' g))
    have hI : star Complex.I = - Complex.I := by simp
    rw [star_add, star_add, star_mul, hI]
    have h2 := Complex.I_mul_I
    linear_combination (1 / 2 : ℂ) * (star (T v g) * T' v' g - star (T' v g) * T v' g
      - Complex.I * star (T' v g) * T' v' g) * h2
  have i1 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g) (μ.restrict 𝓕) :=
    is.sub ia
  have i2 : Integrable (fun g => star ((T + T') v g) * (T + T') v' g - star (T v g) * T v' g
      - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i1.sub ib
  have i3 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g) (μ.restrict 𝓕) := it.sub ia
  have i4 : Integrable (fun g => star ((T + Complex.I • T') v g) * (T + Complex.I • T') v' g
      - star (T v g) * T v' g - star (T' v g) * T' v' g) (μ.restrict 𝓕) := i3.sub ib
  have i5 := i4.const_mul Complex.I
  rw [e]
  refine ⟨(i2.sub i5).const_mul _, ?_⟩
  rw [integral_const_mul, integral_sub i2 i5, integral_const_mul, integral_sub i1 ib, integral_sub i3 ib,
    integral_sub is ia, integral_sub it ia, ea, eb, es, et]
  ring

theorem isMultiplicityInner_inner : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (HM : HMod (MMap M)) (U : Submodule ℂ (MMap M)), HM.Is U (ipM M μ 𝓕) → ∀ x y : HM.H, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) (inner ℂ x y) := by
  intro D V S M μ 𝓕 HM U h x y
  have hip := h.2.2
  have hd : ∀ z : HM.H, ∃ c, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) c := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := hip z z
      unfold ipM at this
      rw [dite_eq_right hn] at this
      exact hz (inner_self_eq_zero.1 this)
  rw [hip]
  apply ipM_spec
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add (f := _)] at hs ht
  rw [map_smul] at ht
  exact ⟨_, exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

end GlobalTheory.SchurPolar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuation
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjVal

open GlobalTheory.IdemSupport

theorem valuation_cP {D : D7} (Q : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.E) :
    (cP Q).valuation D.host.E (star x) = Q.valuation D.host.E x := by
  have : cP Q = Formalism.BasicNotions.Examples₂.PlacesToy.conjW Q := by
    ext r
    have := Formalism.BasicNotions.Examples₂.PlacesToy.mem_conjW_pow Q r 1
    rw [pow_one, pow_one] at this
    rw [this, mem_cP]
    rfl
  rw [this, Formalism.BasicNotions.Examples₂.PlacesToy.valuation_conjW, star_star]

theorem eq_of_le_iff {a b : WithZero (Multiplicative ℤ)}
    (h : ∀ c, c ≠ 0 → (a ≤ c ↔ b ≤ c)) : a = b := by
  have key : ∀ {a b : WithZero (Multiplicative ℤ)}, (∀ c, c ≠ 0 → a ≤ c → b ≤ c) → b ≤ a := by
    intro a b h
    by_cases ha : a = 0
    · by_contra hb
      have hb0 : b ≠ 0 := fun e => hb (by rw [e]; exact zero_le)
      have h1 := h (WithZero.exp (WithZero.log b - 1)) WithZero.exp_ne_zero (by rw [ha]; exact zero_le)
      rw [← WithZero.exp_log hb0, WithZero.exp_le_exp, WithZero.log_exp] at h1
      omega
    · exact h a ha le_rfl
  exact le_antisymm (key fun c hc => (h c hc).2) (key fun c hc => (h c hc).1)

theorem int_iff {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {e : FiniteAdeleRing (𝓞 E) E}
    (h1 : e P = 1) (h0 : ∀ R, R ≠ P → e R = 0) (y : FiniteAdeleRing (𝓞 E) E) {k : E} (hk : k ≠ 0) :
    (∀ R : HeightOneSpectrum (𝓞 E), Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R) ≤ 1) ↔
      Valued.v (y P) ≤ P.valuation E k := by
  have e1 : ∀ R, (e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) R =
      e R * (y R * algebraMap E (R.adicCompletion E) k⁻¹) := fun R => rfl
  have hv : 0 < P.valuation E k := zero_lt_iff.2 (by simpa using hk)
  have e2 : Valued.v ((e * (y * algebraMap E (FiniteAdeleRing (𝓞 E) E) k⁻¹)) P) ≤ 1 ↔
      Valued.v (y P) ≤ P.valuation E k := by
    rw [e1, h1, one_mul, map_mul, Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀, mul_inv_le_iff₀ hv, one_mul]
  rw [← e2]
  refine ⟨fun h => h P, fun h R => ?_⟩
  by_cases hR : R = P
  · rw [hR]; exact h
  · rw [e1, h0 R hR, zero_mul, map_zero]
    exact zero_le

theorem map_three {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B ≃+* C) (a b c : A) :
    g (f (a * (b * c))) = g (f a) * (g (f b) * g (f c)) := by
  simp only [map_mul]

theorem conj_mem_iff {D : D7} (e z : AE D) (k : D.host.E) :
    finPart D (cA D e * (cA D z * incA D (star k)⁻¹)) ∈ intAE D ↔ finPart D (e * (z * incA D k⁻¹)) ∈ intAE D := by
  rw [← star_inv₀, ← cA_incA, ← RingHom.map_mul, ← RingHom.map_mul]
  refine ⟨fun h => ?_, finPart_cA_mem⟩
  have := finPart_cA_mem h
  rwa [cA_cA] at this


set_option maxHeartbeats 800000 in
theorem components_and_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  intro D ι hinc hint hid
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  choose ε hε using hid
  have hd : ∀ P, IsDelta Φ P (ε P) := fun P => (tie_iff hΦ (hε P).1.1 (hε P).2.1 P).1 (hε P).1.2.2
  refine ⟨fun e P h => ?_, fun z Q => ?_⟩
  · rw [delta_unique hΦ (delta_of_isIdemAt hΦ h) (hd P)]
    exact (hε P).2
  have hc : cA D (ε Q) = ε (cP Q) := delta_unique hΦ (delta_conj hΦ (hd Q)) (hd _)
  have key : ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (y : AE D) (k : D.host.E), k ≠ 0 →
      (finPart D (ε P * (y * incA D k⁻¹)) ∈ intAE D ↔ Valued.v (ι (finPart D y) P) ≤ P.valuation D.host.E k) := by
    intro P y k hk
    have : ι (finPart D (incA D k⁻¹)) = algebraMap D.host.E _ k⁻¹ := hinc k⁻¹
    rw [hint, map_three, this]
    exact int_iff (hε P).2.2.1 (hε P).2.2.2 _ hk
  refine eq_of_le_iff fun c hc0 => ?_
  obtain ⟨k, rfl⟩ := Q.valuation_surjective D.host.E c
  have hk : k ≠ 0 := fun e => hc0 (by rw [e, Valuation.map_zero])
  have h1 := key (cP Q) (cA D z) (star k) (star_ne_zero.2 hk)
  rw [valuation_cP, ← hc, conj_mem_iff] at h1
  exact h1.symm.trans (key Q z k hk)

end GlobalTheory.ConjVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_components_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  first | exact @GlobalTheory.ConjVal.components_and_conj_valuation | exact GlobalTheory.ConjVal.components_and_conj_valuation | (intros; apply GlobalTheory.ConjVal.components_and_conj_valuation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifo
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory.SchwartzMajorant

variable (F : Type) [Field F] [NumberField F]

theorem pureA_add_algebraMap {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (ξ : κ → F) (x : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.pureA F f g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j) =
      f ((fun j => mixedEmbedding F (ξ j)) + fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1) *
      g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + fun j => (x j).2) := by
  unfold GlobalTheory.WeilM.pureA
  congr 2
  funext j
  simp only [Pi.add_apply]
  rw [show (algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j).1 = (algebraMap F (AdeleRing (𝓞 F) F) (ξ j)).1 + (x j).1 from rfl,
    map_add, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem norm_le_of_decay {V : Type} [NormedAddCommGroup V] {φ : V → ℂ} {k : ℕ} {C0 Ck : ℝ}
    (h0 : ∀ v, ‖φ v‖ ≤ C0) (hk : ∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) (w a : V) :
    ‖φ (w + a)‖ * (1 + ‖w‖) ^ k ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k := by
  set u := w + a with hu
  have hCk : 0 ≤ Ck := le_trans (by positivity) (hk 0)
  have hC0 : 0 ≤ C0 := le_trans (norm_nonneg _) (h0 0)
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have h1 : ‖φ u‖ * (1 + ‖u‖) ^ k ≤ 2 ^ k * (C0 + Ck) := by
    rcases le_total ‖u‖ 1 with hu1 | hu1
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ C0 * 2 ^ k :=
            mul_le_mul (h0 u) (pow_le_pow_left₀ (by positivity) (by linarith) k) (by positivity) hC0
        _ ≤ _ := by nlinarith
    · calc ‖φ u‖ * (1 + ‖u‖) ^ k ≤ ‖φ u‖ * (2 * ‖u‖) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k) (norm_nonneg _)
        _ = 2 ^ k * (‖u‖ ^ k * ‖φ u‖) := by rw [mul_pow]; ring
        _ ≤ 2 ^ k * Ck := mul_le_mul_of_nonneg_left (hk u) h2k.le
        _ ≤ _ := by nlinarith
  have h2 : (1 + ‖w‖) ^ k ≤ (1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k := by
    rw [← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    have : ‖w‖ ≤ ‖u‖ + ‖a‖ := by
      calc ‖w‖ = ‖u - a‖ := by rw [hu, add_sub_cancel_right]
        _ ≤ ‖u‖ + ‖a‖ := norm_sub_le _ _
    nlinarith [norm_nonneg u, norm_nonneg a]
  calc ‖φ u‖ * (1 + ‖w‖) ^ k ≤ ‖φ u‖ * ((1 + ‖a‖) ^ k * (1 + ‖u‖) ^ k) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = (‖φ u‖ * (1 + ‖u‖) ^ k) * (1 + ‖a‖) ^ k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)

theorem summable_one_add_norm_pow_inv {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] :
    Summable fun z : L => ((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹ := by
  refine Summable.of_norm_bounded_eventually (ZLattice.summable_norm_pow_inv L _ (Nat.lt_succ_self _)) ?_
  refine (Set.finite_singleton (0 : L)).subset fun z hz => ?_
  by_contra h0
  apply hz
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 h0
  show ‖((1 + ‖z‖) ^ (Module.finrank ℤ L + 1))⁻¹‖ ≤ ‖z‖⁻¹ ^ (Module.finrank ℤ L + 1)
  rw [norm_inv, norm_pow, Real.norm_of_nonneg (by positivity), inv_pow]
  exact inv_anti₀ (pow_pos hz0 _) (pow_le_pow_left₀ hz0.le (by linarith) _)

theorem exists_majorant_pureA {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) (x : κ → AdeleRing (𝓞 F) F) :
    ∃ k : ℕ, ∃ M : (κ → F) → ℝ, Summable M ∧ ∀ (C0 Ck : ℝ) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
      (∀ v, ‖φ v‖ ≤ C0) → (∀ v, ‖v‖ ^ k * ‖φ v‖ ≤ Ck) → ∀ ξ : κ → F,
        ‖GlobalTheory.WeilM.pureA F φ g (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ (C0 + Ck) * M ξ := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  let xf : κ → FiniteAdeleRing (𝓞 F) F := fun j => (x j).2
  let a : κ → mixedEmbedding.mixedSpace F := fun j => InfiniteAdeleRing.ringEquiv_mixedSpace F (x j).1
  have hK : IsCompact ((fun y => y - xf) '' tsupport g) :=
    hg.2.isCompact.image (continuous_id.sub continuous_const)
  obtain ⟨N, hN, hKN⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hK
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  let v : (κ → F) → (κ → mixedEmbedding.mixedSpace F) := fun ξ j => mixedEmbedding F (ξ j)
  let S : Set (κ → F) := {ξ | v ξ ∈ GlobalTheory.WeilM.denomLattice F κ N}
  let k := Module.finrank ℤ (GlobalTheory.WeilM.denomLattice F κ N) + 1
  refine ⟨k, S.indicator fun ξ => 2 ^ k * (1 + ‖a‖) ^ k * B * ((1 + ‖v ξ‖) ^ k)⁻¹, ?_, ?_⟩
  · rw [← summable_subtype_iff_indicator]
    let j : S → GlobalTheory.WeilM.denomLattice F κ N := fun ξ => ⟨v ξ, ξ.2⟩
    have hj : Function.Injective j := fun p q h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    exact ((summable_one_add_norm_pow_inv (GlobalTheory.WeilM.denomLattice F κ N)).comp_injective hj).mul_left _
  · intro C0 Ck φ h0 hk ξ
    rw [pureA_add_algebraMap, norm_mul]
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hd := norm_le_of_decay h0 hk (v ξ) a
      have hpos : 0 < (1 + ‖v ξ‖) ^ k := by positivity
      have h1 : ‖φ (v ξ + a)‖ ≤ 2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hd
      calc ‖φ (v ξ + a)‖ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖
          ≤ (2 ^ k * (C0 + Ck) * (1 + ‖a‖) ^ k * ((1 + ‖v ξ‖) ^ k)⁻¹) * B :=
            mul_le_mul h1 (hB _) (norm_nonneg _) (le_trans (norm_nonneg _) h1)
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hξ, mul_zero]
      have hz : g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf) = 0 := by
        by_contra h0'
        apply hξ
        have hmem : (fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) ∈ (fun y => y - xf) '' tsupport g :=
          ⟨_, subset_tsupport _ h0', add_sub_cancel_right _ _⟩
        show ∀ i, (N : ℝ) • v ξ i ∈ mixedEmbedding.integerLattice F
        intro i
        obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun w => by
          rw [map_mul, map_natCast]
          exact hKN _ hmem i w
        refine ⟨y, ?_⟩
        have h2 := congrArg (mixedEmbedding F) hy
        rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
        exact h2.symm
      show _ * ‖g ((fun j => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ j)) + xf)‖ ≤ 0
      rw [hz, norm_zero, mul_zero]

theorem exists_summable_majorant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type}
    [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  intro F _ _ κ _ P _ Ψ p0 m g f hg hΨ hC x
  choose k M hM hbound using fun i => exists_majorant_pureA F (hg i) x
  choose C hCev using hC
  refine ⟨fun ξ => ∑ i, (C 0 + C (k i)) * M i ξ, summable_sum fun i _ => (hM i).mul_left _, ?_⟩
  have hall : ∀ᶠ p in nhds p0, ∀ i, (∀ v, ‖v‖ ^ 0 * ‖f p i v‖ ≤ C 0) ∧
      (∀ v, ‖v‖ ^ k i * ‖f p i v‖ ≤ C (k i)) :=
    Filter.eventually_all.2 fun i => ((hCev 0).and (hCev (k i))).mono fun p hp => ⟨hp.1 i, hp.2 i⟩
  filter_upwards [hΨ, hall] with p hp hb ξ
  rw [hp, Finset.sum_apply]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => hbound i _ _ _ (fun v => ?_) (hb i).2 ξ)
  simpa using (hb i).1 v

end GlobalTheory.SchwartzMajorant
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSummableMajorantAdelicSchwartzLocallyUnifoStatement
open NumberField IsDedekindDomain
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_summableMajorant_adelicSchwartz_locallyUniform : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {P : Type} [TopologicalSpace P]
    (Ψ : P → (κ → AdeleRing (𝓞 F) F) → ℂ) (p0 : P) (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (f : P → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
    (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) →
    (∀ᶠ p in nhds p0, Ψ p = ∑ i, GlobalTheory.WeilM.pureA F (f p i) (g i)) →
    (∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C) →
    ∀ x : κ → AdeleRing (𝓞 F) F, ∃ M : (κ → F) → ℝ, Summable M ∧
      ∀ᶠ p in nhds p0, ∀ ξ : κ → F, ‖Ψ p (fun j => algebraMap F (AdeleRing (𝓞 F) F) (ξ j) + x j)‖ ≤ M ξ := by
  first | exact @GlobalTheory.SchwartzMajorant.exists_summable_majorant | exact GlobalTheory.SchwartzMajorant.exists_summable_majorant | (intros; apply GlobalTheory.SchwartzMajorant.exists_summable_majorant <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrandPeriodic
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SWQ GlobalTheory.GaugeEx
open scoped Matrix Pointwise

namespace GlobalTheory.ThetaTransform

variable {F : Type} [Field F] [NumberField F] {N : ℕ} [Invertible (2 : AF F)] {ψ : AddChar (AF F) ℂ}

theorem integrand_periodic {f : VA F N → ℂ} (hf : QuasiV ψ f) (x y : Fin N → AF F) (b : Fin N → F) :
    f (x, rat b + y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ (rat b + y)))) = f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y))) := by
  have h0 : (rat (0 : Fin N → F) : Fin N → AF F) = 0 := by funext l; simp [rat]
  have h := hf 0 b (x, y)
  rw [h0, Prod.mk_add_mk, zero_add] at h
  rw [h, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm]
  congr 2
  simp only [symV, dotProduct_add, zero_dotProduct]
  ring

theorem invV_heisV_fst (ν : Measure (AF F)) (𝓓 : Set (Fin N → AF F)) (f : VA F N → ℂ) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (u, 0) f) x = invV ψ ν 𝓓 f (x + u) := by
  unfold invV
  congr 1
  funext y
  rw [heisV, mul_right_comm, ← AddChar.map_add_eq_mul, mul_comm, Prod.mk_add_mk, add_zero]
  congr 2
  simp only [symV, add_dotProduct, dotProduct_zero]
  ring

theorem invV_heisV_snd {ν : Measure (AF F)} (hν : IsCov1 ν) {𝓓 : Set (Fin N → AF F)}
    (hD : IsAddFundamentalDomain (ratSub F N) 𝓓 (muV N ν)) {f : VA F N → ℂ} (hf : QuasiV ψ f) (u x : Fin N → AF F) :
    invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * invV ψ ν 𝓓 f x := by
  obtain ⟨hH, hmem, -, -, -⟩ := GlobalTheory.SWQ.rat_lattice_fundamentalDomain F N ν hν
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : Countable (ratSub F N) := by
    refine Set.Countable.to_subtype ((Set.countable_range (rat : (Fin N → F) → (Fin N → AF F))).mono fun v hv => ?_)
    obtain ⟨ξ, h⟩ := (hmem v).1 hv
    exact ⟨ξ, h.symm⟩
  let P : (Fin N → AF F) → ℂ := fun y => f (x, y) * ψ (-(⅟(2 : AF F) * (x ⬝ᵥ y)))
  have hP : ∀ (g : ratSub F N) (y : Fin N → AF F), P (g +ᵥ y) = P y := by
    rintro ⟨g, hg⟩ y
    obtain ⟨ξ, rfl⟩ := (hmem g).1 hg
    exact integrand_periodic hf x y ξ
  have e1 : invV ψ ν 𝓓 (heisV ψ (0, u) f) x = ψ (x ⬝ᵥ u) * ∫ y in 𝓓, P (y + u) ∂(muV N ν) := by
    unfold invV
    rw [← integral_const_mul]
    congr 1
    funext y
    simp only [heisV, P, Prod.mk_add_mk, add_zero]
    rw [mul_right_comm, ← AddChar.map_add_eq_mul, mul_left_comm, ← AddChar.map_add_eq_mul, mul_comm]
    congr 2
    simp only [symV, dotProduct_add, zero_dotProduct]
    linear_combination two_mul_invOf (x ⬝ᵥ u)
  rw [e1]
  congr 1
  have hmp : MeasurePreserving (fun y : Fin N → AF F => y + u) (muV N ν) (muV N ν) := measurePreserving_add_right _ u
  have hemb : MeasurableEmbedding (fun y : Fin N → AF F => y + u) := measurableEmbedding_addRight u
  have hD' : IsAddFundamentalDomain (ratSub F N) (u +ᵥ 𝓓) (muV N ν) := hD.vadd_of_comm u
  have e2 : 𝓓 = (fun y : Fin N → AF F => y + u) ⁻¹' (u +ᵥ 𝓓) := by
    ext y
    rw [Set.mem_preimage, add_comm]
    exact Set.vadd_mem_vadd_set_iff.symm
  conv_lhs => rw [e2]
  rw [hmp.setIntegral_preimage_emb hemb P]
  exact hD'.setIntegral_eq hD hP

end GlobalTheory.ThetaTransform

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

namespace GlobalTheory.LBLift

section Alg

variable {R : Type} [CommRing R] (I : Ideal R) {D T : Type} [Category.{0} D] [Category.{0} T]

def In1 (F : D ⥤ CommAlgCat.{0} R) (f : C1 F) : Prop :=
  ∀ (t t' : D) (a : t ⟶ t'), f t t' a ∈ I.map (algebraMap R (F.obj t'))

def In2 (F : D ⥤ CommAlgCat.{0} R) (z : C2 F) : Prop :=
  ∀ (t t' t'' : D) (a : t ⟶ t') (b : t' ⟶ t''), z t t' t'' a b ∈ I.map (algebraMap R (F.obj t''))

variable {F : D ⥤ CommAlgCat.{0} R} {F' : T ⥤ CommAlgCat.{0} R}

def PrimI (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') : Prop :=
  ∀ (z : Z2 F) (f : C1 F'), In2 I F z.1 → In1 I F' f →
    d1 F' f = (n₀.pullbackTwoCocycle z).1 - (n₁.pullbackTwoCocycle z).1 - (n₂.pullbackTwoCocycle z).1 → ∃ f₀ : C1 F, In1 I F f₀ ∧ d1 F f₀ = z.1

def mdef (F : D ⥤ CommAlgCat.{0} R) (u : C1 F) : C2 F :=
  fun t t' t'' a b ↦ mp F b (u t t' a) * u t' t'' b - u t t'' (a ≫ b)

def MulRel (n₀ n₁ n₂ : CoefMap (RingHom.id R) F F') (u : C1 F) (v : C0 F') : Prop :=
  In1 I F' fun t t' a ↦ n₀.α t' (u _ _ (n₀.G.map a)) * v t' -
    n₁.α t' (u _ _ (n₁.G.map a)) * n₂.α t' (u _ _ (n₂.G.map a)) * mp F' a (v t)

end Alg

section Geo

variable {R : Type} [CommRing R] {X X₀ Y : Scheme.{0}} {D T : Type} [Category.{0} D] [Category.{0} T]

structure IsBasis (G : D ⥤ AffOp X) : Prop where
  cover : ∀ (x : X) (U : X.Opens), x ∈ U → ∃ t : D, x ∈ (G.obj t).unop.1 ∧ (G.obj t).unop.1 ≤ U
  dir : ∀ (t₁ t₂ : D) (x : X) (U : X.Opens), x ∈ U → x ∈ (G.obj t₁).unop.1 → x ∈ (G.obj t₂).unop.1 →
    ∃ t₃ : D, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ x ∈ (G.obj t₃).unop.1 ∧ (G.obj t₃).unop.1 ≤ U

def pullMap {s : X ⟶ Sp R} {s' : Y ⟶ Sp R} {φ : Y ⟶ X} (w : φ ≫ s = s' ≫ spMap (RingHom.id R))
    (G : D ⥤ AffOp X) (H : T ⥤ AffOp Y) (K : T ⥤ D)
    (le : ∀ t, (H.obj t).unop.1 ≤ φ ⁻¹ᵁ (G.obj (K.obj t)).unop.1) :
    CoefMap (RingHom.id R) (G ⋙ OAff s) (H ⋙ OAff s') where
  G := K
  α t := CechDR.secPull s s' ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩
  naturality {p q} a b :=
    (congrArg (fun t ↦ t.hom b) (φ.map_appLE (le q) (homOfLE (leOfHom (G.map (K.map a)).unop)).op)).trans
      (congrArg (fun t ↦ t.hom b) (φ.appLE_map (le p) (homOfLE (leOfHom (H.map a).unop)).op)).symm
  smul t := semiHom_secPull w ⟨((H.obj t).unop, (G.obj (K.obj t)).unop), le t⟩

structure IsThick (I : Ideal R) (s : X ⟶ Sp R) (i : X₀ ⟶ X) : Prop where
  closed : IsClosedImmersion i
  surj : Surjective i
  app_surj : ∀ U : X.affineOpens, Function.Surjective (i.app U.1).hom
  ker : ∀ (U : X.affineOpens) (b : Sec s U.1), (i.app U.1).hom b = 0 ↔ b ∈ I.map (algebraMap R (Sec s U.1))

def Small (i : X₀ ⟶ X) (L : LB X₀) : Type := {p : X.affineOpens × L.ι // i ⁻¹ᵁ p.1.1 ≤ L.U p.2}

instance (i : X₀ ⟶ X) (L : LB X₀) : Preorder (Small i L) := Preorder.lift fun p ↦ p.1.1

def smallG (i : X₀ ⟶ X) (L : LB X₀) : (Small i L)ᵒᵖ ⥤ AffOp X :=
  (Monotone.functor (f := fun p : Small i L ↦ p.1.1) fun _ _ h ↦ h).op

theorem Small.le_inf {i : X₀ ⟶ X} {L : LB X₀} {p q : (Small i L)ᵒᵖ} (a : p ⟶ q) :
    i ⁻¹ᵁ q.unop.1.1.1 ≤ L.U p.unop.1.2 ⊓ L.U q.unop.1.2 :=
  _root_.le_inf (fun _ hx ↦ p.unop.2 ((show q.unop.1.1 ≤ p.unop.1.1 from leOfHom a.unop) hx)) q.unop.2

def IsLift (s : X ⟶ Sp R) (i : X₀ ⟶ X) (L : LB X₀) (u : C1 (smallG i L ⋙ OAff s)) : Prop :=
  ∀ (p q : (Small i L)ᵒᵖ) (a : p ⟶ q),
    (i.app q.unop.1.1.1).hom (u p q a) = (res (Small.le_inf a) (L.g p.unop.1.2 q.unop.1.2)).val

end Geo


open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic in
attribute [local instance] Over.cartesianMonoidalCategory in
def AbLift : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R), I ^ 2 = ⊥ → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom →
    ∀ (X₀ Y₀ : Scheme.{0}) (i : X₀ ⟶ A.left) (i' : Y₀ ⟶ (A ⊗ A).left) (ψ₀ ψ₁ ψ₂ : Y₀ ⟶ X₀),
      IsThick I A.hom i → IsThick I (A ⊗ A).hom i' → ψ₀ ≫ i = i' ≫ (μ[A]).left → ψ₁ ≫ i = i' ≫ (fst A A).left →
      ψ₂ ≫ i = i' ≫ (snd A A).left →
      ∀ c : Pic X₀, CechPic.pull ψ₀ c = CechPic.pull ψ₁ c + CechPic.pull ψ₂ c → ∃ c' : Pic A.left, CechPic.pull i c' = c

end GlobalTheory.LBLift
end
end
