module

public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProduct
public import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta
public import Development.WeilBound.ThetaLifts.LeviDeterminants.DqStmt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModels

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.WeilRepRationalDarbouxFixesThetaDistribution
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace PositivityTheory.ThKF0.Resc

section Gen

variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] {c : K →ₐ[R] K}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem ug_smul {v : K} (hv : IsUnit v) (J : Matrix β β K) : UG c (v • J) = UG c J := by
  ext g
  change (g : Matrix β β K)ᵀ * (v • J) * (g : Matrix β β K).map c = v • J ↔
    (g : Matrix β β K)ᵀ * J * (g : Matrix β β K).map c = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hv.smul_left_cancel

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (v : K) (J : Matrix β β K) : dbl (v • J) = v • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_smul {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix α β K) :
    symp c ξ' (u • JA) (v • JB) x y = symp c ξ JA JB x y := by
  rw [symp, symp, h]
  congr 1
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable [Invertible (2 : R)]

theorem isWeilB_resc {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ}
    {d : Darboux (symp c ξ JA JB) κ} {χ : Kˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hW : IsWeilB c C ψ ξ JA JB d χ om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsWeilB c C ψ ξ' JA' JB' d' χ om' ∧ ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  obtain ⟨hS, dd, omd, hdd, hSd, hR, hbox⟩ := hW
  have hU : UG c (v • JB) = UG c JB := ug_smul hv JB
  have hUd : UG c (dbl (v • JB)) = UG c (dbl JB) := by rw [dbl_smul]; exact ug_smul hv _
  refine ⟨⟨d.e, fun w w' => (symp_smul h JA JB w w').trans (d.form w w')⟩, om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
      ⟨dd.e, fun w w' => by rw [dbl_smul]; exact (symp_smul h JA _ w w').trans (dd.form w w')⟩,
      omd.comp (Subgroup.inclusion hUd.le), hdd,
      ⟨fun g => hSd.pres _, fun g => hSd.impl (Subgroup.inclusion hUd.le g), fun g => hSd.adm _⟩,
      fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hUd.le p) t hp,
      fun g gd hg => hbox (Subgroup.inclusion hU.le g) (Subgroup.inclusion hUd.le gd) hg⟩,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_isQuad (hσ : IsCMExt F E σ) : ∃ δ : E, IsQuad σ δ := by
  obtain ⟨-, hc, h2, hτ⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hi : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [h] at this
    exact this.symm
  have h0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  have ha : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hi, neg_sub]
  have hl : LinearIndependent F ![(1 : E), x - σ x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have h4 := hst
    rw [Algebra.smul_def, Algebra.smul_def] at h1 h4
    rw [map_add (f := _), map_mul, map_mul, σ.commutes, σ.commutes, map_one, ha, map_zero] at h1
    have h3 : algebraMap F E (s + s) = 0 := by
      rw [map_add (f := _)]
      linear_combination h4 + h1
    have hs : s = 0 := add_self_eq_zero.1 ((map_eq_zero _).1 h3)
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.1 hst).resolve_right h0⟩
  refine ⟨x - σ x, h0.isUnit, ha, basisOfLinearIndependentOfCardEqFinrank hl (by simp [h2]), ?_, ?_⟩ <;>
    simp

theorem exists_ratCoord (h2 : Module.finrank F E = 2) {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (he : ∀ x : Matrix α β E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F), ∀ x,
      e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) := by
  choose y z h using he
  have inj := AdeleRing.algebraMap_injective (𝓞 F) F
  have hadd : ∀ a b : Matrix α β E, incM F (a + b) = incM F a + incM F b := fun a b => by
    ext i j; simp [incM]
  have hsm : ∀ (t : F) (a : Matrix α β E), incM F (t • a) = algebraMap F (AF F) t • incM F a := fun t a => by
    ext i j
    change (1 : AF F) ⊗ₜ[F] (t • a i j) = algebraMap F (AF F) t • ((1 : AF F) ⊗ₜ[F] a i j)
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  let f : Matrix α β E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have := h (a + b)
        rw [hadd, map_add (f := _), h, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · simpa using (congrFun (congrArg Prod.fst this) i).symm
        · simpa using (congrFun (congrArg Prod.snd this) i).symm
      map_smul' := fun t a => by
        have := h (t • a)
        rw [hsm, map_smul, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · exact (congrFun (congrArg Prod.fst this) i).symm.trans (map_mul (algebraMap F (AF F)) t (y a i)).symm
        · exact (congrFun (congrArg Prod.snd this) i).symm.trans (map_mul (algebraMap F (AF F)) t (z a i)).symm }
  have hf : Function.Injective f := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h3 : z a = z b := congrArg Prod.snd hab
    have : incM F a = incM F b := e.injective (by rw [h, h, h1, h3])
    exact Matrix.map_injective (Algebra.TensorProduct.includeRight_injective inj) this
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  refine ⟨f.linearEquivOfInjective hf ?_, h⟩
  rw [Module.finrank_matrix, h2, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hκ]
  ring

theorem member (hσ : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ a b : E} (hq : IsQuad σ δ)
    (hab : -1 = δ * a * b) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : IsHerm σ (a • JA)) (hB : IsHerm σ (b • JB))
    {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    (hd : ∀ x : Matrix α β E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    {χ : Chr F E} (hχ : IsHecke F E χ) {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (g : UG (cA σ) (incM F JB)) (γ : Matrix β β E) (hg : (g.1 : Matrix β β (AE F E)) = incM F γ) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hsm : ∀ {ι : Type} (t : E) (J : Matrix ι ι E), incM F (t • J) = inclR (F := F) (AF F) t • incM F J := fun t J => by
    ext i j; simp [incM]
  obtain ⟨d', om', he, hW, hom⟩ := isWeilB_resc (ξ' := inclR (F := F) (AF F) δ)
    (by rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]) (hb.isUnit.map (inclR (F := F) (AF F))) (hsm a JA) (hsm b JB) h
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord hσ.2.2.1 hκ d.e hd
  obtain ⟨g', hg', e⟩ := hom g
  rw [← e]
  refine GlobalTheory.T.seesaw_theta_dual_pair F E σ δ α β κ (a • JA) (b • JB) ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 hq hA hB d' d₀
    (fun x => by rw [← hd₀, ← he]; rfl) χ om' (fun z u hu => ?_) hW g' ⟨γ, by rw [hg']; exact hg⟩
  have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
    (algebraMap F (AF F)).injective).nontrivial
  have hz : z ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
  rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
  exact hχ.2 _

omit [NumberField E] in
theorem rat_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, (γ.1 : Matrix (Fin n) (Fin n) (AE F E)) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g₀, by rw [← hg₀]; rfl⟩

end PositivityTheory.ThKF0.Resc

namespace PositivityTheory.ThKF0

open Resc

theorem darboux_coordinates_rational_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, d', hd', hA⟩ := hom.isWeilPair
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  have eX : IsHerm σ ((1 : E) • JX) := by rw [one_smul]; exact ⟨hX, hXd.isUnit⟩
  have eW : IsHerm σ ((-δ⁻¹) • JW) := by
    refine ⟨fun i j => by simp [hW i j, hq.anti], Ne.isUnit ?_⟩
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hWd
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := rfl
    rw [e, hd']
    exact hco xᵀ
  have e : om (γ, γ') Φ = om.comp (MonoidHom.inl _ _) γ (om.comp (MonoidHom.inr _ _) γ' Φ) := by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  rw [e, member hσ hψ hq (by field_simp) (by simp [Nat.mul_comm]) eW eX hco' hχW hA γ g₀ hg₀ _ (hB.1.pres γ' Φ hΦ)]
  exact member hσ hψ hq (by field_simp) (by simp) eX eW hco hχX hB γ' g₀' hg₀' Φ hΦ

end PositivityTheory.ThKF0
end
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.ThetaGrow
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.AdelicThetaSumNormLePolynomialScale
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0.LatSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := _root_.GlobalTheory.LatScaleSum.thetaSum_norm_le_pow

end PositivityTheory.ThKF0.LatSum

namespace PositivityTheory.ThKF0

theorem theta_sum_norm_bound_denominator : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k :=
  LatSum.thetaSum_norm_le_pow

end PositivityTheory.ThKF0
end

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace PositivityTheory.ThKF0

def ArchBd : Prop := ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ g h (x : Fin n × Fin d → AF F),
    ‖om (g, h) Φ x‖ * (1 + ‖fun i => evI F (x i)‖) ^ N ≤ C * ((ht g : ℝ) * ht h) ^ k

theorem theta_moderate_growth_of_decay (harch : ArchBd) : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ‖theta om Φ g h‖ ≤ C * ((ht g : ℝ) * ht h) ^ k := by
  have hlat := theta_sum_norm_bound_denominator
  have hfin := weil_rep_bounded_denominator
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  obtain ⟨N₀, k₂, C₂, hL⟩ := hlat F (Fin n × Fin d)
  obtain ⟨C₁, k₁, hA⟩ := harch F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ N₀
  obtain ⟨C₃, k₃, hF⟩ := hfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  refine ⟨|C₂| * |C₁| * |C₃| ^ k₂, k₁ + k₃ * k₂, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hsupp⟩ := hF g h
  set H : ℝ := (ht g : ℝ) * ht h with hH
  have hH0 : 0 ≤ H := by rw [hH]; positivity
  have hb := hL (C₁ * H ^ k₁) m (om (g, h) Φ) hm1 (fun ξ => hA g h _) hsupp
  have hA0 : 0 ≤ C₁ * H ^ k₁ :=
    le_trans (by positivity) (hA g h (fun i => algebraMap F (AF F) ((0 : Fin n × Fin d → F) i)))
  have hm0 : (0 : ℝ) ≤ (m : ℝ) ^ k₂ := by positivity
  have hmk : (m : ℝ) ^ k₂ ≤ (|C₃| * H ^ k₃) ^ k₂ :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _))) _
  have hC1 : C₁ * H ^ k₁ ≤ |C₁| * H ^ k₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hH0 _)
  show ‖thetaSum F (om (g, h) Φ)‖ ≤ _
  calc ‖thetaSum F (om (g, h) Φ)‖ ≤ C₂ * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ := hb
    _ ≤ |C₂| * (C₁ * H ^ k₁) * (m : ℝ) ^ k₂ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hA0) hm0
    _ ≤ |C₂| * (|C₁| * H ^ k₁) * (|C₃| * H ^ k₃) ^ k₂ :=
        mul_le_mul (mul_le_mul_of_nonneg_left hC1 (abs_nonneg _)) hmk hm0 (mul_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) (pow_nonneg hH0 _)))
    _ = |C₂| * |C₁| * |C₃| ^ k₂ * H ^ (k₁ + k₃ * k₂) := by rw [pow_add, pow_mul]; ring

end PositivityTheory.ThKF0
end

section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.EvChange
section -- merged from Development.WeilBound.ThetaLifts.LeviDeterminants.EvLine
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct SchwartzMap LineDeriv

namespace PositivityTheory.ThKF0.Line

open PositivityTheory.ThKF0.Lib

section LineProof
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def chirp (c : ℝ) (q : V → ℝ) (x : V) : ℂ := Complex.exp (Complex.I * ((-(2 * Real.pi) * c * q x : ℝ) : ℂ))

theorem chirp_tg (c : ℝ) {q : V → ℝ} (hq : q.HasTemperateGrowth) : (chirp c q).HasTemperateGrowth := by
  have h1 : (fun x => -(2 * Real.pi) * c * q x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const _).mul hq
  exact GlobalTheory.CompanionTheory.OM.SchDiff.temperate_exp.comp h1

theorem hl_schwartz (a : V) (L : V →L[ℝ] ℝ) (f : 𝓢(V, ℂ)) (t : ℝ) : ∃ G : 𝓢(V, ℂ), ∀ x, G x = hl a L t f x := by
  have hq : (fun x => t * L x + t ^ 2 * (L a / 2)).HasTemperateGrowth :=
    ((Function.HasTemperateGrowth.const t).mul L.hasTemperateGrowth).add (Function.HasTemperateGrowth.const _)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (chirp 1 fun x => t * L x + t ^ 2 * (L a / 2))
    (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f), fun x => ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply_apply (chirp_tg 1 hq), SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add, hl, chirp]
  simp only [smul_eq_mul]
  congr 2
  push_cast
  ring

end LineProof

end PositivityTheory.ThKF0.Line
end
end

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0.Change

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def finPr {κ : Type} (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) : (κ → Af F) → ℂ :=
  fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)

theorem pure_eq {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = pureA F f (finPr φ) := rfl

theorem finPr_mem {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB _)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : finPr φ ∈ SB _ :=
  ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩

theorem exists_finPr_ne {κ : Type} [Fintype κ] (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (h0 : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) : ∃ y, finPr φ y ≠ 0 := by
  have key : ∀ v : Pl (F := F), ∃ p : κ → Fv F v, φ v p ≠ 0 ∧
      (φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 → ∀ i, p i ∈ v.adicCompletionIntegers F) := by
    intro v
    obtain ⟨p, hp⟩ := Function.ne_iff.1 (h0 v)
    refine ⟨p, hp, fun h => ?_⟩
    rw [h] at hp
    exact Set.mem_of_indicator_ne_zero hp
  choose p hp hp' using key
  refine ⟨fun i => ⟨fun v => p v i, ?_⟩, ?_⟩
  · filter_upwards [hstd] with v hv using hp' v hv i
  · exact finprod_induction (fun z : ℂ => z ≠ 0) one_ne_zero (fun a b ha hb => mul_ne_zero ha hb) fun v => hp v

def pt {κ : Type} (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

theorem pureA_pt {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ)
    (x : κ → mixedEmbedding.mixedSpace F) (y : κ → Af F) : pureA F f g (pt x y) = f x * g y := by
  simp only [pureA, pt, RingEquiv.apply_symm_apply]

theorem mem_span_finPr {κ : Type} [Fintype κ] (g) (hg : g ∈ SB (κ → Af F)) :
    g ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) ∧
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
      p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)} := by
  obtain ⟨m, c, φ, h1, h2, rfl⟩ := Span.exists_sum_finprod hg
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨φ k, h1 k, h2 k, rfl⟩)

section

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem pol_map (M M' : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (D D' : Matrix (Fin n) (Fin d) (AE F E) → SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hD : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ ↔ f₁ = D u f)
    (hD' : ∀ u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M'.heisLine ψ u) f f₁ ↔ f₁ = D' u f)
    (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) (hb : Function.Bijective ei)
    (hi : ∀ u, At (evI F) u → ∀ f, ei (D u f) = D' u (ei f)) : (M.Pol ψ τ).map ei = M'.Pol ψ τ := _root_.GlobalTheory.ThK.ModelPol.pol_map M M' ψ τ D D' hD hD' ei hb hi


open PositivityTheory.ThKF0.Lib (dop aOf lOf hl) in
open scoped Classical in
theorem inter (hDq : SchwartzDq) (M M' : Model σ X W) (A : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (hA : ∀ u, At (evI F) u → ∀ (f G : SInf F (Fin n × Fin d)) (t : ℝ), (∀ x, G x = hl (aOf M u) (lOf M u) t f x) →
      ∀ x, A G x = hl (aOf M' u) (lOf M' u) t (A f) x) {u} (hu : At (evI F) u) (f) :
    A (dop (aOf M u) (lOf M u) f) = dop (aOf M' u) (lOf M' u) (A f) := by
  choose G hG using Line.hl_schwartz (aOf M u) (lOf M u) f
  ext x
  have h1 := hDq _ _ _ f G hG ((BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A)
  have e : (fun t => ((BoundedContinuousFunction.evalCLM ℂ x ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ) ∘L A) (G t)) =
      fun t => hl (aOf M' u) (lOf M' u) t (A f) x := funext fun t => hA u hu f (G t) t (hG t) x
  rw [e] at h1
  exact h1.unique (Lib.hasDerivAt_hl _ _ (A f) x)

end

theorem change_core {B : Base F E} (hψ : IsStd B.ψ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M M' : Model σ X W}
    (hM : M.IsGood B.ψ) (hM' : M'.IsGood B.ψ) {e : Fn F n d →ₗ[ℂ] Fn F n d} (hE : IsEv B M M' 1 1 ∅ e)
    (hbij : Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _)) :
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), Function.Surjective ei ∧
        (SchwartzDq → (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)) = M'.Pol B.ψ B.emb) ∧
        (∀ v, ev v (M.vac v) = M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
          e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  classical
  obtain ⟨ei, ev, -, hv, hl⟩ := hE.loc
  have hg : finPr M.vac ∈ SB _ := finPr_mem _ (fun v => (hM.vac v).1) hM.std
  have hg' : finPr M'.vac ∈ SB _ := finPr_mem _ (fun v => (hM'.vac v).1) hM'.std
  obtain ⟨y, hy⟩ := exists_finPr_ne M.vac (fun v => (hM.vac v).2.1) hM.std
  obtain ⟨y', hy'⟩ := exists_finPr_ne M'.vac (fun v => (hM'.vac v).2.1) hM'.std
  have mem : ∀ (f : SInf F (Fin n × Fin d)) g, g ∈ SB (Fin n × Fin d → Af F) → pureA F f g ∈ schA F (Fin n × Fin d) :=
    fun f g h => Submodule.subset_span ⟨f, g, h, rfl⟩
  have hvac : ∀ f : SInf F (Fin n × Fin d), e (pureA F f (finPr M.vac)) = pureA F (ei f) (finPr M'.vac) := fun f => by
    have := hl f M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)
    simp only [fun v => (hv v).1] at this
    exact this
  have hinj : Function.Injective ei := (injective_iff_map_eq_zero ei).2 fun f hf => by
    have h1 : e (pureA F f (finPr M.vac)) = e 0 := by
      rw [hvac, hf, map_zero]; funext x; simp [pureA]
    have h2 := hbij.injOn (mem f _ hg) (zero_mem _) h1
    refine SchwartzMap.ext fun x => ?_
    have h3 := congrFun h2 (pt x y)
    rw [pureA_pt] at h3
    exact (mul_eq_zero.1 h3).resolve_right hy
  have hsl : ∀ Φ ∈ schA F (Fin n × Fin d), ∃ f, ∀ x, e Φ (pt x y') = ei f x := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | zero => exact ⟨0, fun x => by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨f, hf⟩ := ha
      obtain ⟨g, hg⟩ := hb
      exact ⟨f + g, fun x => by simp [hf, hg]⟩
    | smul c a _ ha =>
      obtain ⟨f, hf⟩ := ha
      exact ⟨c • f, fun x => by simp [hf]⟩
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      replace hg := mem_span_finPr g hg
      induction hg using Submodule.span_induction with
      | zero => exact ⟨0, fun x => by
          rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; simp⟩
      | add a b _ _ ha hb =>
        obtain ⟨f₁, hf⟩ := ha
        obtain ⟨f₂, hg⟩ := hb
        exact ⟨f₁ + f₂, fun x => by
          rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; simp [hf, hg]⟩
      | smul c a _ ha =>
        obtain ⟨f₁, hf⟩ := ha
        exact ⟨c • f₁, fun x => by
          rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; simp [hf]⟩
      | mem p hp =>
        obtain ⟨φ, hφ, hs, rfl⟩ := hp
        have h1 := hl f φ hφ (by filter_upwards [hs, hM.std] with v h1 h2 using h1.trans h2.symm)
        refine ⟨finPr (fun v => ev v (φ v)) y' • f, fun x => ?_⟩
        rw [pure_eq, pure_eq] at h1
        refine (congrFun h1 _).trans ?_
        rw [pureA_pt]
        simp [mul_comm]
  have hsurj : Function.Surjective ei := fun g => by
    obtain ⟨Φ, hΦ, h1⟩ := hbij.surjOn (mem g _ hg')
    obtain ⟨f, hf⟩ := hsl Φ hΦ
    refine ⟨(finPr M'.vac y')⁻¹ • f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    have h2 := hf x
    rw [h1, pureA_pt] at h2
    rw [map_smul, smul_apply, ← h2, smul_eq_mul]
    field_simp
  have Heisenberg₂ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = M'.co.rho B.ψ u (e Φ) := by
    intro u Φ hΦ
    have h1 : ∀ m : ℕ, incM F (1 : Matrix (Fin m) (Fin m) E) = 1 := fun m => Matrix.map_one _ (map_zero _) (map_one _)
    have := hE.Heisenberg₂ u Φ hΦ
    rwa [h1, h1, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨ei, ev, hsurj, fun hDq => ?_, hv, hl⟩
  have key : ∀ (N : Model σ X W) u, At (evI F) u → ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (N.heisLine B.ψ u) f f₁ ↔
      f₁ = Lib.dop (Lib.aOf N u) (Lib.lOf N u) f := fun N u hu f f₁ =>
    ⟨Lib.actsD_unique N hψ hu, fun h => h ▸ Lib.actsD_dop N hψ hu f⟩
  refine pol_map M M' B.ψ B.emb _ _ (key M) (key M') _ ⟨hinj, hsurj⟩ fun u hu f => inter hDq M M' ei (fun u hu f G t hG x => ?_) hu f
  have e1 : M.heisLine B.ψ u t (pureA F f (finPr M.vac)) = pureA F G (finPr M.vac) := by
    rw [← Lib.tens_rOf, Lib.heisLine_tens M hψ hu f (Lib.rOf_add _) t,
      Lib.tens_rOf]
    congr 1
    exact funext fun x => (hG x).symm
  have e2 : e (M.heisLine B.ψ u t (pureA F f (finPr M.vac))) = M'.heisLine B.ψ u t (e (pureA F f (finPr M.vac))) :=
    Heisenberg₂ _ _ (mem f _ hg)
  rw [e1, hvac, hvac, ← Lib.tens_rOf (ei f),
    Lib.heisLine_tens M' hψ hu (ei f) (Lib.rOf_add _) t, Lib.tens_rOf] at e2
  have := congrFun e2 (pt x y')
  rw [pureA_pt, pureA_pt] at this
  exact mul_right_cancel₀ hy' this

end PositivityTheory.ThKF0.Change
end
end
