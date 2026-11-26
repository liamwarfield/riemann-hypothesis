module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiExteriorTensorSmoothIrreducibleIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullOfValuesSesq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCharpolySelfReciprocal
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_X_sub_C' (μ : ℂ) : (X - C μ : ℂ[X]).reverse = 1 - C μ * X := by
  have h1 : (1 : ℂ[X]).reverse = 1 := by simp only [reverse, natDegree_one, reflect_one, pow_zero]
  have hX : (X : ℂ[X]).reverse = 1 := by simpa [h1] using reverse_X_mul (1 : ℂ[X])
  rw [sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg, neg_mul, ← sub_eq_add_neg]

theorem prod_conj_reverse (s : Multiset ℂ) (hs : ∀ z ∈ s, ‖z‖ = 1) :
    (((s.map fun z => X - C z).prod).map (starRingEnd ℂ)).reverse =
      C (conj (((s.map fun z => X - C z).prod).coeff 0)) * (s.map fun z => X - C z).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [reverse]
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 := fun z hz => hs z (Multiset.mem_cons_of_mem hz)
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have hca : conj a * a = 1 := by
      rw [Complex.conj_mul', ha]; simp
    rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, reverse_mul_of_domain, ih hs',
      mul_coeff_zero]
    have hlin : ((X - C a : ℂ[X]).map (starRingEnd ℂ)).reverse = C (-conj a) * (X - C a) := by
      rw [Polynomial.map_sub, map_X, map_C, reverse_X_sub_C']
      have hw : C (conj a) * C a = (1 : ℂ[X]) := by rw [← C_mul, hca, C_1]
      rw [C_neg]
      linear_combination (-1 : ℂ[X]) * hw
    have hc0 : (X - C a : ℂ[X]).coeff 0 = -a := by simp
    rw [hlin, hc0, map_mul, C_mul]
    simp only [map_neg]
    ring

end GlobalTheory.ConjSelfRecip

namespace GlobalTheory.ConjSelfRecip

open ComplexConjugate

theorem reverse_map_inj {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) (Q : R[X]) : (Q.map f).reverse = Q.reverse.map f := by
  rw [reverse, reverse, natDegree_map_eq_of_injective hf, reflect_map]

theorem ell_conj_selfRecip : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    P.coeff 0 ≠ 0 ∧ C (IsCMField.complexConj E (P.coeff 0)) * P =
      (P.map (IsCMField.complexConj E).toRingEquiv.toRingHom).reverse := by
  intro E _ _ _ n P hP
  obtain ⟨hm, -, -, hroots⟩ := hP
  let τ : E →+* ℂ := Classical.choice inferInstance
  have hQm : (P.map τ).Monic := hm.map τ
  have hQ : ((P.map τ).roots.map fun z => X - C z).prod = P.map τ :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm IsAlgClosed.card_roots_eq_natDegree
  have hr : ∀ z ∈ (P.map τ).roots, ‖z‖ = 1 := hroots τ
  have key := prod_conj_reverse (P.map τ).roots hr
  rw [hQ] at key
  constructor
  · intro h0
    have h0' : (0 : ℂ) ∈ (P.map τ).roots := by
      rw [mem_roots hQm.ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map, h0, map_zero]
    have := hr 0 h0'
    simp at this
  · apply Polynomial.map_injective τ τ.injective
    have hcomp : τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom = (starRingEnd ℂ).comp τ := by
      ext x
      simp [IsCMField.complexEmbedding_complexConj]
    rw [Polynomial.map_mul, map_C, ← reverse_map_inj τ τ.injective, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, key, coeff_map]
    congr 2
    simp [IsCMField.complexEmbedding_complexConj]

end GlobalTheory.ConjSelfRecip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaBoundVp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (betaBound_vp cE_vp c_vp delta_vp a0 n_vp IsClassZetaVals)
open GlobalTheory.CMVal (OF IsBaseCond expIn)

namespace GlobalTheory.DenExist

section Field

variable {E : Type} [Field E] [NumberField E]

theorem finite_support (d s : ℕ) {I : Type} [Fintype I] (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : 𝔣 ≠ ⊥)
    (z : ClassGroup (OF E) → ℚ) :
    {l : ℕ | l.Prime ∧ (⌈betaBound_vp d s κ 𝔣 z l / 12⌉₊ : ℕ) ≠ 0}.Finite := by
  set A : Set ℕ := {l | l.Prime ∧ ∃ v : HeightOneSpectrum (OF E), v.asIdeal ∣ 𝔣 ∧ (l : OF E) ∈ v.asIdeal} with hAdef
  have hA : A.Finite :=
    GlobalTheory.FunObj.SqNum.finite_primes_under (K := maximalRealSubfield E) (p := fun v => v.asIdeal ∣ 𝔣)
      (Ideal.finite_factors h𝔣)
  let B : Finset ℕ := (Finset.univ.biUnion fun C =>
    (z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)).den.primeFactors) ∪ (discr E).natAbs.primeFactors
  refine (hA.union B.finite_toSet).subset ?_
  rintro l ⟨hl, hn⟩
  by_contra hc
  simp only [Set.mem_union, not_or, Finset.mem_coe] at hc
  obtain ⟨hlA, hlB⟩ := hc
  apply hn
  have hv : ∀ v : HeightOneSpectrum (OF E), (l : OF E) ∈ v.asIdeal → ¬ v.asIdeal ∣ 𝔣 :=
    fun v h1 h2 => hlA ⟨hl, v, h2, h1⟩
  have ha0 : a0 𝔣 l = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply csSup_le'
    rintro _ ⟨v, h1, rfl⟩
    simp [expIn, multiplicity_eq_zero_of_not_dvd (hv v h1)]
  have hcv : c_vp 𝔣 l = 0 := by
    have hd : ¬ l ∣ (discr E).natAbs := fun h => hlB (Finset.mem_union_right _
      (Nat.mem_primeFactors.2 ⟨hl, h, by simpa using discr_ne_zero E⟩))
    rw [c_vp, if_neg (fun ⟨v, h1, h2⟩ => hv v h1 h2), delta_vp]
    simp [padicValInt, padicValNat.eq_zero_of_not_dvd hd]
  have hcE : cE_vp l z = 0 := by
    rw [cE_vp, ← bot_eq_zero, Finset.sup_eq_bot_iff]
    intro C _
    set q := z C / 2 ^ Module.finrank ℚ (maximalRealSubfield E)
    have hd : ¬ l ∣ q.den := fun h => hlB (Finset.mem_union_left _ (Finset.mem_biUnion.2
      ⟨C, Finset.mem_univ _, Nat.mem_primeFactors.2 ⟨hl, h, q.den_ne_zero⟩⟩))
    show (-padicValRat l q).toNat = 0
    rw [Int.toNat_eq_zero, padicValRat, padicValNat.eq_zero_of_not_dvd hd]
    simp
  simp [betaBound_vp, hcE, hcv, ha0, n_vp]

end Field

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem exists_denom (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hb : IsBaseCond (condF G.pl)) (i j : Fin D.R.m) (s : ℕ) (hs : 1 ≤ s) :
    ∃ n, IsDenom G i j s n ∧ {l | l.Prime ∧ n l ≠ 0}.Finite := by
  obtain ⟨⟨z, hz'⟩, -⟩ := @hz D.host.E _ _ hcm s hs
  refine ⟨fun l => ((⌈betaBound_vp D.host.d s (kap D sc.cGap i j s) (condF G.pl) z l / 12⌉₊ : ℕ) : ℝ),
    ⟨z, hz', fun l _ => rfl⟩, ?_⟩
  refine (finite_support D.host.d s (kap D sc.cGap i j s) (condF G.pl) hb.1 z).subset ?_
  rintro l ⟨hl, h⟩
  exact ⟨hl, fun h' => h (by simp only [h', Nat.cast_zero])⟩

theorem denEx (hz : GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators) (hF : FieldDat) : DenEx := by
  obtain ⟨CF0, h⟩ := hF
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => ?_⟩
  obtain ⟨hcm, -, -, hb, -⟩ := h C hC D large₂ he hx hR T Lc μ₀ hL G
  exact fun i j s hs _ => exists_denom hz G hcm hb i j s hs

end GlobalTheory.DenExist

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTr
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchRhoPure


variable (F : Type) [Field F] [NumberField F] in
def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply {F : Type} [Field F] [NumberField F] (a : AF F) : evHom F a = evI F a := rfl

theorem rho_pureA_schrF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ ψ JA JB d hψ u hu f h
  have hw : At (evI F) (d.e u) := fun r hr => by rw [← map_smul, hu r hr, map_zero]
  show schr ψ (d.e u) (pureA F f h) = _
  generalize d.e u = w at hw ⊢
  obtain ⟨p, q⟩ := w
  funext x
  have hfin : (fun i => ((x + p) i).2) = fun i => (x i).2 := by
    funext i
    have h0 : evI F ((0, 1) : AF F) = 0 := map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    have h1 : (1 : Af F) * (p i).2 = 0 := congrArg (fun z : (κ → AF F) × (κ → AF F) => (z.1 i).2) (hw _ h0)
    change (x i).2 + (p i).2 = _
    rw [one_mul] at h1
    rw [h1, add_zero]
  have hAt : At (evI F) (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q)) := by
    intro v hv
    have hq : v • q = 0 := congrArg Prod.snd (hw v hv)
    rw [smul_add, ← dotProduct_smul, smul_eq_mul, mul_left_comm, ← smul_eq_mul v, ← dotProduct_smul, hq]
    simp
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + p) i).1) =
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) + ArchUniq.locV p :=
    funext fun i => map_add (evHom F) (x i) (p i)
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (x ⬝ᵥ q + ⅟(2 : AF F) * (p ⬝ᵥ q))) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i)) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, evI F (p i) * evI F (q i)) / 2 := by
    set z : mixedEmbedding.mixedSpace F := ∑ i, evI F (p i) * evI F (q i) with hz
    have hpq : evHom F (p ⬝ᵥ q) = z := by
      rw [RingHom.map_dotProduct]; rfl
    have hxq : evHom F (x ⬝ᵥ q) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * evI F (q i) := by
      rw [RingHom.map_dotProduct]; rfl
    have key : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) +
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evHom F ⅟(2 : AF F) * z) =
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z := by
      rw [← map_add (f := _), ← add_mul, ← map_add (f := _), invOf_two_add_invOf_two, map_one, one_mul]
    rw [← evHom_apply, map_add (f := _), map_mul, hpq, hxq, map_add (f := _)]
    linarith
  simp only [schr, pureA, GlobalTheory.ArchUniq.schrF, GlobalTheory.ArchUniq.trP, GlobalTheory.ArchUniq.locV] at harch ⊢
  rw [hψ.2.2 _ hAt, hfin, htr, harch, ← mul_assoc]

end GlobalTheory.ArchRhoPure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTrStatement
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix RealInnerProductSpace
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ), IsStd ψ → ∀ u : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (h : (κ → Af F) → ℂ),
      d.rho ψ u (pureA F f h) = pureA F (GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ)
        (GlobalTheory.ArchUniq.locV (d.e u).1, GlobalTheory.ArchUniq.locV (d.e u).2) f) h := by
  first | exact @GlobalTheory.ArchRhoPure.rho_pureA_schrF | exact GlobalTheory.ArchRhoPure.rho_pureA_schrF | (intros; apply GlobalTheory.ArchRhoPure.rho_pureA_schrF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval.ConjLoc

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def conjSchR (κ : Type) [Fintype κ] : SInf F κ →L[ℝ] SInf F κ :=
  SchwartzMap.postcompCLM (Complex.conjCLE : ℂ →L[ℝ] ℂ)

theorem conjSchR_apply {κ : Type} [Fintype κ] (f : SInf F κ) (x : κ → mixedEmbedding.mixedSpace F) :
    conjSchR κ f x = starRingEnd ℂ (f x) := rfl

def conjSchCLM {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (T : SInf F κ →L[ℂ] SInf F κ₁) : SInf F κ →L[ℂ] SInf F κ₁ where
  toFun f := conjSchR κ₁ (T (conjSchR κ f))
  map_add' f g := by simp only [map_add (f := _)]
  map_smul' c f := by
    have h : conjSchR κ (c • f) = starRingEnd ℂ c • conjSchR κ f := by
      refine SchwartzMap.ext fun y => ?_; simp only [conjSchR_apply, SchwartzMap.smul_apply, smul_eq_mul, map_mul]
    refine SchwartzMap.ext fun x => ?_
    rw [h, map_smul, conjSchR_apply, RingHom.id_apply, SchwartzMap.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      smul_eq_mul, map_mul, Complex.conj_conj, conjSchR_apply]
  cont := (conjSchR κ₁).continuous.comp (T.continuous.comp (conjSchR κ).continuous)

theorem conj_mem_SB {X : Type} [TopologicalSpace X] {φ : X → ℂ} (h : φ ∈ SB X) :
    (fun x => starRingEnd ℂ (φ x)) ∈ SB X :=
  ⟨h.1.comp (starRingEnd ℂ), h.2.comp_left (g := starRingEnd ℂ) (map_zero _)⟩

theorem conj_stdInd_apply (κ : Type) (v : Pl (F := F)) (y : κ → Fv F v) :
    starRingEnd ℂ (stdInd F κ v y) = stdInd F κ v y := by
  unfold stdInd
  by_cases hy : y ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
  · rw [Set.indicator_of_mem hy, Pi.one_apply, map_one]
  · rw [Set.indicator_of_notMem hy, map_zero]

theorem conj_stdInd (κ : Type) (v : Pl (F := F)) :
    (fun y => starRingEnd ℂ (stdInd F κ v y)) = stdInd F κ v :=
  funext (conj_stdInd_apply κ v)

theorem conj_pure {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (x : κ → AF F) :
    starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) x := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, conjSchR_apply, map_mul]
  congr 1
  exact MulEquiv.map_finprod (starRingAut : ℂ ≃+* ℂ).toMulEquiv _

theorem isLocOp_conjLin {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ)
    (he : IsLocOp e) : IsLocOp (conjLin e) := by
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  refine ⟨conjSchCLM ei, fun v => conjLin (ev v), fun v φ hφ => conj_mem_SB (hSB v _ (conj_mem_SB hφ)), ?_, ?_⟩
  · filter_upwards [hstd] with v hv
    funext y
    rw [conjLin_apply, conj_stdInd, hv, conj_stdInd_apply]
  · intro f φ hφ hfin
    funext y
    rw [conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x)) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (conjSchR κ f) (fun v y => starRingEnd ℂ (φ v y)) :=
      funext (conj_pure f φ)
    have hfin' : ∀ᶠ v in cofinite, (fun y => starRingEnd ℂ (φ v y)) = stdInd F κ v := by
      filter_upwards [hfin] with v hv
      rw [hv, conj_stdInd]
    rw [h1, hloc _ _ (fun v => conj_mem_SB (hφ v)) hfin', conj_pure]
    rfl

end GlobalTheory.DblEval.ConjLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperatorStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_local_operator : ∀ {F : Type} [Field F] [NumberField F] {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ), IsLocOp e → IsLocOp (conjLin e) := by
  first | exact @GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | exact GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin | (intros; apply GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

namespace GlobalTheory.RegSSClass

theorem nilpotent_eq_zero_of_commute_sep_alg {K : Type} [Field K] [IsAlgClosed K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  set f := Matrix.toLin' A
  have hcp : f.charpoly = A.charpoly := Matrix.charpoly_toLin' A
  have hfg : Commute f (Matrix.toLin' N) := hc.map Matrix.toLinAlgEquiv'
  have hNl : IsNilpotent (Matrix.toLin' N) := hN.map Matrix.toLinAlgEquiv'
  obtain ⟨k, hk⟩ := hNl
  have key : ∀ μ, Module.End.maxGenEigenspace f μ ≤ LinearMap.ker (Matrix.toLin' N) := fun μ v hv => by
    have h1 : Module.finrank K (Module.End.maxGenEigenspace f μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq, hcp]; exact Polynomial.rootMultiplicity_le_one_of_separable hA μ
    by_cases h0 : v = 0
    · simp [h0]
    have h2 : Module.finrank K (Module.End.maxGenEigenspace f μ) = 1 := le_antisymm h1
        (Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun h => h0 (congrArg Subtype.val h)⟩)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨v, hv⟩ : Module.End.maxGenEigenspace f μ)
        fun h => h0 (congrArg Subtype.val h)).1 h2 ⟨_, Module.End.mapsTo_maxGenEigenspace_of_comm hfg μ hv⟩
    have hc' : Matrix.toLin' N v = c • v := (congrArg Subtype.val hc).symm
    have hpow : ∀ m : ℕ, (Matrix.toLin' N ^ m) v = c ^ m • v := by
      intro m
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hc', smul_smul, pow_succ]
    have h5 : c ^ k • v = 0 := by rw [← hpow, hk]; rfl
    have hc0 : c = 0 := by
      rcases smul_eq_zero.1 h5 with h | h
      · exact pow_eq_zero_iff'.1 h |>.1
      · exact absurd h h0
    rw [LinearMap.mem_ker, hc', hc0, zero_smul]
  have h3 := iSup_le key
  rw [Module.End.iSup_maxGenEigenspace_eq_top, top_le_iff, LinearMap.ker_eq_top] at h3
  exact Matrix.toLin'.injective (by rw [h3, map_zero])

theorem nilpotent_eq_zero_of_commute_sep {K : Type} [Field K] {n : ℕ}
    {A N : Matrix (Fin n) (Fin n) K} (hA : A.charpoly.Separable) (hN : IsNilpotent N) (hc : Commute A N) :
    N = 0 := by
  have h := nilpotent_eq_zero_of_commute_sep_alg (K := AlgebraicClosure K)
    (A := A.map (algebraMap K (AlgebraicClosure K))) (N := N.map (algebraMap K (AlgebraicClosure K)))
    (by rw [Matrix.charpoly_map]; exact hA.map) (hN.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
    (hc.map (algebraMap K (AlgebraicClosure K)).mapMatrix)
  ext i j
  have := congrFun (congrFun h i) j
  simpa using this

theorem isSemisimple_of_charpoly_separable {K : Type} [Field K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly.Separable) : Module.End.IsSemisimple (Matrix.toLin' A) := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := A.charpoly) h.squarefree ?_
  have := LinearMap.aeval_self_charpoly (Matrix.toLin' A)
  rwa [Matrix.charpoly_toLin'] at this

theorem charpoly_eq_of_isConj {K : Type} [Field K] {n : ℕ} {G : Subgroup (GL (Fin n) K)} {a b : G}
    (h : IsConj a b) : b.1.1.charpoly = a.1.1.charpoly := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  simpa using Matrix.charpoly_units_conj c.1 a.1.1

end GlobalTheory.RegSSClass

open GlobalTheory.RegSSClass in
theorem GlobalTheory.regSS_conjClass_isSSClass : ∀ {D : D7} {V : HSp D} (γ : GF V), IsRegSS γ.1.1 → IsSSClass {δ : GF V | IsConj γ δ} := by
  intro D V γ hγ
  have hs : γ.1.1.charpoly.Separable := hγ
  refine ⟨γ, isSemisimple_of_charpoly_separable hs, ?_⟩
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨x, ⟨isSemisimple_of_charpoly_separable ?_, Commute.refl _, by simp⟩, hx⟩
    rw [charpoly_eq_of_isConj hx]; exact hs
  · rintro ⟨s, ⟨_, hcomm, hnil⟩, hconj⟩
    have hss : s.1.1.charpoly.Separable := by rw [charpoly_eq_of_isConj hconj]; exact hs
    have h0 := nilpotent_eq_zero_of_commute_sep hss hnil (hcomm.symm.sub_right (Commute.refl _))
    have hxs : x = s := Subtype.ext (Units.ext (sub_eq_zero.1 h0))
    rw [hxs]; exact hconj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSmul
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

namespace GlobalTheory.ArchDecay

section Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def heisD (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (u : Matrix (Fin n) (Fin d) (AE F E))
    (f : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → AF F) : ℂ :=
  deriv (fun t : ℝ => M.heisLine ψ u t f x) 0

def liftI (M : Model σ X W)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    Matrix (Fin n) (Fin d) (AE F E) :=
  M.co.e.symm (fun i => infAd F (ζ.1 i), fun i => infAd F (ζ.2 i))

def movI (M : Model σ X W) (p : UA σ X.J × UA σ W.J)
    (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)) :
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  (arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).1, arch F (M.co.e (actAB (cA σ) p⁻¹ (liftI M ζ))).2)

def wordH (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (zs : List ((Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)))
    (f : (Fin n × Fin d → AF F) → ℂ) : (Fin n × Fin d → AF F) → ℂ :=
  zs.foldr (fun ζ g => heisD M ψ (liftI M ζ) g) f

end Model

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (ζ : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  dD F ζ.1 f + c • mM F (T ζ.2) f

def wordR (T : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ((κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)) (c : ℂ)
    (zs : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) (f : (κ → AF F) → ℂ) :
    (κ → AF F) → ℂ :=
  zs.foldr (dR F T c) f

theorem dD_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : κ → mixedEmbedding.mixedSpace F)
    (c : ℂ) (f : (κ → AF F) → ℂ) : dD F v (c • f) = c • dD F v f := by
  funext x
  simp only [dD, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_mul_field']

theorem mM_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (c : ℂ) (f : (κ → AF F) → ℂ) : mM F l (c • f) = c • mM F l f := by
  funext x
  simp only [mM, Pi.smul_apply, smul_eq_mul]
  ring

theorem app_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (o : Op F κ) (c : ℂ)
    (f : (κ → AF F) → ℂ) : app F o (c • f) = c • app F o f := by
  cases o with
  | inl v => exact dD_smul v c f
  | inr l => exact mM_smul l c f

theorem dD_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    dD F 0 f = 0 := by
  funext x
  have e : ∀ t : ℝ, (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i)) = x := by
    intro t
    funext i
    have h0 : infAd F (0 : mixedEmbedding.mixedSpace F) = 0 := by unfold infAd; rw [map_zero, map_zero]
    show x i + infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i) = x i
    rw [Pi.zero_apply, smul_zero, h0, add_zero]
  show deriv (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) 0 = 0
  rw [show (fun t : ℝ => f (x + fun i => infAd F (t • (0 : κ → mixedEmbedding.mixedSpace F) i))) = fun _ => f x from
    funext fun t => by rw [e t]]
  exact deriv_const 0 (f x)

theorem mM_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : (κ → AF F) → ℂ) :
    mM F 0 f = 0 := by
  funext x
  simp [mM]

end GlobalTheory.ArchDecay
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveMulVecMapBasis
namespace GlobalTheory.BasisLeftInverse

theorem exists_left_inv {E : Type} [Field E] {n d : ℕ} (B : Matrix (Fin n) (Fin d) E)
    (h : LinearIndependent E B.col) : ∃ C : Matrix (Fin d) (Fin n) E, C * B = 1 := by
  have hinj : Function.Injective B.mulVec := Matrix.mulVec_injective_iff.2 h
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' B, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

theorem injective_mulVec_map_basis {E : Type} [Field E] {n : ℕ} (V : Submodule E (Fin n → E))
    (τ : E →+* ℂ) :
    Function.Injective (Matrix.mulVec (Matrix.of fun (k : Fin n) (i : Fin (Module.finrank E V)) =>
      τ (((Module.finBasis E V i : V) : Fin n → E) k))) := by
  let B : Matrix (Fin n) (Fin (Module.finrank E V)) E :=
    Matrix.of fun k i => ((Module.finBasis E V i : V) : Fin n → E) k
  have hB : LinearIndependent E B.col :=
    (Module.finBasis E V).linearIndependent.map' V.subtype (Submodule.ker_subtype V)
  obtain ⟨C, hC⟩ := exists_left_inv B hB
  have hC' : C.map τ * B.map τ = 1 := by
    rw [← Matrix.map_mul, hC, Matrix.map_one τ (map_zero τ) (map_one τ)]
  change Function.Injective (B.map τ).mulVec
  intro v w hvw
  have h1 : Matrix.mulVec (C.map τ * B.map τ) v = Matrix.mulVec (C.map τ * B.map τ) w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hvw]
  rwa [hC', Matrix.one_mulVec, Matrix.one_mulVec] at h1

end GlobalTheory.BasisLeftInverse
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositive
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.UnitaryClasses

theorem gramOn_one_map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ =
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ)ᴴ *
      (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k)) := by
  ext i j
  simp [gramOn, hform, Matrix.mul_apply, Matrix.one_apply, Matrix.conjTranspose_apply,
    IsCMField.complexEmbedding_complexConj, mul_ite, ite_mul, Finset.sum_ite_eq]

theorem gramOn_basis_mulVec_injective {E : Type} [Field E] {n : ℕ}
    (V : Submodule E (Fin n → E)) (τ : E →+* ℂ) :
    Function.Injective (Matrix.of fun k i => τ ((Module.finBasis E V i).1 k) :
        Matrix (Fin n) (Fin (Module.finrank E V)) ℂ).mulVec := by
  first
  | exact @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis
  | (apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BasisLeftInverse.injective_mulVec_map_basis ..)

theorem gramOn_one_det_totallyPositive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  intro E _ _ _ n V
  have key : ∀ τ : E →+* ℂ, 0 < τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det := by
    intro τ
    rw [RingHom.map_det]
    have : τ.mapMatrix (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V) =
        (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).map τ := rfl
    rw [this, gramOn_one_map_eq]
    exact (Matrix.PosDef.conjTranspose_mul_self _ (gramOn_basis_mulVec_injective V τ)).det_pos
  refine ⟨fun h0 => ?_, fun τ => ?_⟩
  · have τ0 := (Classical.arbitrary (NumberField.InfinitePlace E)).embedding
    have := key τ0
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  · have h := Complex.lt_def.mp (key τ)
    refine ⟨(τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det).re, h.1, ?_⟩
    apply Complex.ext
    · simp
    · simpa using h.2.symm

end GlobalTheory.UnitaryClasses
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDetHermitianTotallyPositiveStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_hermitian_totally_positive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (V : Submodule E (Fin n → E)), (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det ≠ 0 ∧ ∀ τ : E →+* ℂ, ∃ r : ℝ, 0 < r ∧ τ (gramOn (IsCMField.complexConj E).toRingEquiv.toRingHom 1 V).det = r := by
  first | exact @GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive | exact GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive | (intros; apply GlobalTheory.UnitaryClasses.gramOn_one_det_totallyPositive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartz
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay LineDeriv

namespace GlobalTheory.ArchDecay.SchAStab

variable (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem pureA_line (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) (t : ℝ) :
    pureA F f g (x + fun i => infAd F (t • v i)) = f (arch F x + t • v) * g (fun i => (x i).2) := by
  unfold pureA
  congr 2
  · funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F
        ((x i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t • v i)) = evI F (x i) + t • v i
    rw [map_add (f := _), RingEquiv.apply_symm_apply]
    rfl
  · funext i
    exact add_zero (x i).2

theorem hasDerivAt_line (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) (v : κ → mixedEmbedding.mixedSpace F) :
    HasDerivAt (fun t : ℝ => pureA F f g (x + fun i => infAd F (t • v i)))
      (fderiv ℝ f (arch F x) v * g (fun i => (x i).2)) 0 := by
  simp only [pureA_line]
  have h1 : HasDerivAt (fun t : ℝ => arch F x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (arch F x)
  have h2 : HasDerivAt (fun t : ℝ => f (arch F x + t • v)) (fderiv ℝ f (arch F x) v) 0 :=
    (f.differentiableAt (x := arch F x)).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
  exact h2.mul_const _

theorem dD_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (v : κ → mixedEmbedding.mixedSpace F) : dD F v (pureA F f g) = pureA F (∂_{v} f : SchwartzMap _ ℂ) g := by
  funext x
  rw [dD, (hasDerivAt_line F f g x v).deriv]
  show _ = (∂_{v} f : SchwartzMap _ ℂ) (arch F x) * _
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]

def mulL (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  SchwartzMap.smulLeftCLM ℂ (⇑l) f

theorem mulL_apply (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ)
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (y : κ → mixedEmbedding.mixedSpace F) :
    mulL F l f y = (l y : ℂ) * f y := by
  rw [mulL, SchwartzMap.smulLeftCLM_apply_apply l.hasTemperateGrowth, Complex.real_smul]

theorem mM_pureA (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) : mM F l (pureA F f g) = pureA F (mulL F l f) g := by
  funext x
  simp only [mM, pureA, mulL_apply, mul_assoc]
  rfl

theorem mem_schA_mM (l : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    mM F l Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    rw [mM_pureA]
    exact Submodule.subset_span ⟨mulL F l f, g, hg, rfl⟩
  | zero =>
    have : mM F l (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [mM]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    have : mM F l (Φ + Ψ) = mM F l Φ + mM F l Ψ := by funext x; simp [mM, mul_add]
    rw [this]; exact Submodule.add_mem _ h1 h2
  | smul a Φ _ h =>
    have : mM F l (a • Φ) = a • mM F l Φ := by funext x; simp [mM]; ring
    rw [this]; exact Submodule.smul_mem _ a h

theorem archimedeanDirectionalDerivative_mem_adelicSchwartz (v : κ → mixedEmbedding.mixedSpace F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    (∀ x : κ → AF F, DifferentiableAt ℝ (fun t : ℝ => Φ (x + fun i => infAd F (t • v i))) 0) ∧
      dD F v Φ ∈ schA F κ := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine ⟨fun x => (hasDerivAt_line F f g x v).differentiableAt, ?_⟩
    rw [dD_pureA]
    exact Submodule.subset_span ⟨_, g, hg, rfl⟩
  | zero =>
    refine ⟨fun x => differentiableAt_const _, ?_⟩
    have : dD F v (0 : (κ → AF F) → ℂ) = 0 := by funext x; simp [dD]
    rw [this]; exact Submodule.zero_mem _
  | add Φ Ψ _ _ h1 h2 =>
    refine ⟨fun x => (h1.1 x).add (h2.1 x), ?_⟩
    have : dD F v (Φ + Ψ) = dD F v Φ + dD F v Ψ := by
      funext x
      simp only [dD, Pi.add_apply]
      exact deriv_add (h1.1 x) (h2.1 x)
    rw [this]; exact Submodule.add_mem _ h1.2 h2.2
  | smul a Φ _ h =>
    refine ⟨fun x => (h.1 x).const_mul a, ?_⟩
    have : dD F v (a • Φ) = a • dD F v Φ := by
      funext x
      simp only [dD, Pi.smul_apply, smul_eq_mul]
      exact deriv_const_mul a (h.1 x)
    rw [this]; exact Submodule.smul_mem _ a h.2

theorem app_mem_schA : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ),
    ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  intro F _ _ κ _ o f hf
  rcases o with v | l
  · exact (archimedeanDirectionalDerivative_mem_adelicSchwartz F v hf).2
  · exact mem_schA_mM F l hf

end GlobalTheory.ArchDecay.SchAStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanDecayOperatorApplyMemAdelicSchwartzStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanDecayOperatorApply_mem_adelicSchwartz : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (o : Op F κ), ∀ f ∈ schA F κ, app F o f ∈ schA F κ := by
  first | exact @GlobalTheory.ArchDecay.SchAStab.app_mem_schA | exact GlobalTheory.ArchDecay.SchAStab.app_mem_schA | (intros; apply GlobalTheory.ArchDecay.SchAStab.app_mem_schA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (k : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})
    (fun _ N => N ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) k

theorem fockDeg_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    fockDeg M ψ τ 0 = Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀} := rfl

theorem fockDeg_succ (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ (k + 1) = fockDeg M ψ τ k ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
      ActsD (evI F) (M.heisLine ψ u) f f₁} := rfl

def lowDegInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : ℕ :=
  sInf {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}

def lowPartInf (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) : Submodule ℂ P :=
  (fockDeg M B.ψ B.emb (lowDegInf B M p)).map p

theorem fockDeg_mono (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    Monotone (fockDeg M ψ τ) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

theorem fockDeg_le_pol (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ k ≤ M.Pol ψ τ := by
  induction k with
  | zero => exact Submodule.span_le.2 fun f hf => Submodule.mem_sInf.2 fun N hN => hN.1 f hf
  | succ k ih =>
    refine sup_le ih (Submodule.span_le.2 ?_)
    rintro f₁ ⟨u, hu, f, hf, hd⟩
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 (ih hf) N hN) f₁ hd

theorem pol_eq_iSup_fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    M.Pol ψ τ = ⨆ k, fockDeg M ψ τ k := by
  refine le_antisymm (sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ hd => ?_⟩) (iSup_le (fockDeg_le_pol M ψ τ))
  · exact Submodule.mem_iSup_of_mem 0 (Submodule.subset_span hf₀)
  · obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M ψ τ).directed_le).1 hf
    exact Submodule.mem_iSup_of_mem (k + 1)
      (Submodule.mem_sup_right (Submodule.subset_span ⟨u, hu, f, hk, hd⟩))

theorem lowPartInf_ne_bot (B : Base F E) (M : Model σ Y W) {P : Type} [AddCommGroup P] [Module ℂ P]
    (p : SInf F (Fin n × Fin d) →ₗ[ℂ] P) (h : ∃ f ∈ M.Pol B.ψ B.emb, p f ≠ 0) : lowPartInf B M p ≠ ⊥ := by
  obtain ⟨f, hf, hp⟩ := h
  rw [pol_eq_iSup_fockDeg] at hf
  obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ (fockDeg_mono M B.ψ B.emb).directed_le).1 hf
  have hne : {k | ∃ f ∈ fockDeg M B.ψ B.emb k, p f ≠ 0}.Nonempty := ⟨k, f, hk, hp⟩
  obtain ⟨g, hg, hpg⟩ := Nat.sInf_mem hne
  intro hbot
  exact hpg ((Submodule.eq_bot_iff _).1 hbot (p g) ⟨g, hg, rfl⟩)

end GlobalTheory.IndLine
end
end
