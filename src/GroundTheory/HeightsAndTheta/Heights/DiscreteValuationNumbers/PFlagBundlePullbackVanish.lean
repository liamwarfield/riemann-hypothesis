module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.JoinCoordMidVar

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFlagBundlePullbackVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagBundlePullbackVanish

theorem liftDeg_eq_pullDeg {K : Type*} (L : K → ℤ) :
    liftDeg L = FieldNumbers.pullDeg Function.Embedding.some L := by
  funext o
  cases o with
  | none =>
    rw [FieldNumbers.pullDeg, Function.extend_apply' _ _ _ (by simp)]
    rfl
  | some k =>
    exact (Function.Embedding.some.injective.extend_apply L 0 k).symm

theorem contract_projIdeal {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
    {K : Type} {ι : K → Type} (y : (Σ k, ι k) → Ω) {N M : ℕ} {E : Type} [AddCommGroup E]
    [Module Ω E] (w : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω E)
    {Φ : Type} [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ) :
    FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ t) =
      pointIdeal (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) F y := by
  let ψ : MvPolynomial K Ω →+* MvPolynomial (Option K) Φ :=
    (rename Option.some).toRingHom.comp (MvPolynomial.map (algebraMap Ω Φ))
  have hψ : Function.Injective ψ :=
    (rename_injective _ (Option.some_injective K)).comp
      (map_injective _ (algebraMap Ω Φ).injective)
  ext x
  simp only [FieldNumbers.contractPrime, projIdeal, pointIdeal, Ideal.mem_comap, RingHom.mem_ker]
  refine Iff.trans ?_ (map_eq_zero_iff ψ hψ)
  refine Iff.of_eq (congrArg (· = 0) ?_)
  induction x using MvPolynomial.induction_on with
  | C r =>
    simp [ψ, pointConeMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, rename_X, eval₂Hom_X', pointConeMap, aeval_X]
    simp [ψ, FieldNumbers.blockIncl, projCoord]
    exact Or.inl rfl

theorem proof (hPF : FieldNumbers.ProjectionFormulaContracted.Statement.{0})
    (hDim : FlagBundleDim.Statement) : FlagBundlePullbackVanish.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV hVdim N E _ _ B w b hflag M a φ hφ Φ _ _ t ht i hi2 hiN L hL
  obtain ⟨hP, hrel⟩ := hDim F Ω K ι y e hV hVdim N E B w b hflag M a φ hφ Φ t ht i (by omega) hiN
  have hlen : (L.map liftDeg).length = e + i - 1 := by simp; omega
  have hrel' : FieldNumbers.relDim (projIdeal F y w φ (truncCoord t i)) =
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by rw [hrel, hlen]
  have hrelV : FieldNumbers.relDim (ι := ι) (pointIdeal F y) =
      (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim, hVdim]
    have : (((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K) = e := by push_cast; ring
    exact congrArg (fun z : ℤ => ((z : WithTop ℤ) : WithBot (WithTop ℤ))) this
  have hcontr : FieldNumbers.relDim
      (FieldNumbers.contractPrime Function.Embedding.some (projIdeal F y w φ (truncCoord t i))) <
      (((L.map liftDeg).length : ℕ) : WithBot (WithTop ℤ)) := by
    rw [contract_projIdeal]
    show FieldNumbers.relDim (ι := ι) (pointIdeal F y) < _
    rw [hrelV, hlen]
    show (((e : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) <
      ((((e + i - 1 : ℕ) : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ))
    exact WithBot.coe_lt_coe.mpr (WithTop.coe_lt_coe.mpr (by omega))
  have hzero := hPF F K (Option K) Function.Embedding.some (bundleIdx ι M)
    (projIdeal F y w φ (truncCoord t i)) hP _ hrel' hcontr
    (fun k => L.get (Fin.cast (by simp) k))
  rw [intNumL, ← hzero]
  congr 1
  funext k
  simp [liftDeg_eq_pullDeg]

end FlagBundlePullbackVanish

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocalizedQuotientIsSimpleModuleOfMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

section Lemmas

def ResidualComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' ≤ divCycle P s G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (liftForm s) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (newVar (some none)) (liftForm m) G' ≤
          ratDiv P f g G

def ExceptionalComparison.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P (d + 1) →
    ∀ (b : K → ℤ) (f g : MRing ι O), IsEffectiveVertical P ϖ b f g →
    ∀ (c : K → ℕ) (s : MRing ι O), IsMultiHomog s c → s ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b f g) →
    ∀ e : K → ℕ, (∀ k, (c k : ℤ) = b k + e k) →
    ∀ m : MRing ι O, IsMultiHomog m e → m ∉ P →
    (∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H → m ∉ H) →
    ∀ G' : Ideal (MRing (extIdx ι (BlowUpIdx ι)) O),
      (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' →
      0 < divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' →
      0 < ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
        (liftForm g * newVar (some none)) G' →
      ∃ G : Ideal (MRing ι O), (C ϖ : MRing ι O) ∈ G ∧
        divCycle (blowUpOf P (blowUpGens s g f m e)) (newVar none) G' +
            ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
              (liftForm g * newVar (some none)) G' ≤ divCycle P s G ∧
        ratDiv (blowUpOf P (blowUpGens s g f m e)) (liftForm (f * m))
            (liftForm g * newVar (some none)) G' ≤ ratDiv P f g G

end Lemmas

section Examples

section Simple

variable {A : Type*} [CommRing A]

end Simple

theorem form_mem_of_divCycle_ne_zero {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P x W ≠ 0) : x ∈ W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  · exact absurd rfl h

section Constants

set_option linter.unusedSectionVars false

variable {K : Type} {ι : K → Type} {J : Type} {O : Type*} [CommRing O] [IsDomain O]

theorem liftForm_const (a : O) : liftForm (J := J) (C a : MRing ι O) = C a :=
  (liftForm (J := J) (ι := ι) (R := O)).commutes a

end Constants

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwistedDualGensSpan
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem TwistedDualGensSpan.sum_mul_mem_localized {R Ω : Type*} [CommRing R] [Field Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {f : Ω} (hf : f ∈ A) {r : ℕ} (a t : Fin r → Ω)
    (ha : ∀ q, ∃ n : ℕ, f ^ n * a q ∈ A) (ht : ∀ q, t q ∈ A) :
    ∃ n : ℕ, f ^ n * ∑ q, a q * t q ∈ A := by
  refine Finset.sum_induction _ (fun x => ∃ n : ℕ, f ^ n * x ∈ A) ?_ ⟨0, by simp⟩ ?_
  · rintro x z ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : f ^ (n + m) * (x + z) = f ^ m * (f ^ n * x) + f ^ n * (f ^ m * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hf _) hn) (mul_mem (pow_mem hf _) hm)
  · intro q _
    obtain ⟨n, hn⟩ := ha q
    exact ⟨n, by rw [← mul_assoc]; exact mul_mem hn (ht q)⟩

theorem TwistedDualGensSpan.proof : TwistedDualGensSpan.Statement := by
  unfold TwistedDualGensSpan.Statement
  intro R _ Ω _ _ K _ ι y N E _ _ B a M φ hφ c hc
  obtain ⟨k, f, cc, hf, hcc, hsum, hb⟩ := B.frame c hc
  choose b hli hsp hiff using hb
  obtain ⟨l0, hl0⟩ : ∃ l0, f l0 ≠ 0 := by
    by_contra! h
    simp [h] at hsum
  obtain ⟨β, hβ⟩ : ∃ β : Module.Basis (Fin N) Ω E, ∀ q, β q = b l0 q :=
    ⟨Module.Basis.mk (hli l0) (hsp l0).ge, fun q => Module.Basis.mk_apply _ _ _⟩
  have key : ∀ q, β.coord q ∈ Submodule.span Ω (Set.range φ) := by
    intro q
    have hden : ∀ l r, ∃ D ∈ chartRing R (segreVec y) c, D ≠ 0 ∧
        (f l ≠ 0 → D * β.coord q (b l r) ∈ chartRing R (segreVec y) c) := by
      intro l r
      by_cases hl : f l = 0
      · exact ⟨1, one_mem _, one_ne_zero, fun h => (h hl).elim⟩
      obtain ⟨n, hn⟩ := (hiff l (b l r)).2 ⟨Pi.single r 1, fun q' => ⟨0, by
        by_cases h : q' = r
        · subst h; simp
        · simp [h]⟩, by simp [Pi.single_apply]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l0 _).1 ⟨0, by simpa using hn⟩
      obtain ⟨m, hm⟩ := ha' q
      refine ⟨f l0 ^ m * f l ^ n, mul_mem (pow_mem (hf l0) _) (pow_mem (hf l) _),
        mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ hl), fun _ => ?_⟩
      have hc' : β.coord q (f l ^ n • b l r) = a' q := by
        rw [hrep, show ∑ q, a' q • b l0 q = ∑ q, a' q • β q by simp [hβ],
          Module.Basis.coord_apply, Module.Basis.repr_sum_self]
      have : f l0 ^ m * f l ^ n * β.coord q (b l r) = f l0 ^ m * a' q := by
        rw [← hc', map_smul, smul_eq_mul]; ring
      rw [this]
      exact hm
    choose D hDA hD0 hDc using hden
    set d : Ω := ∏ p : Fin k × Fin N, D p.1 p.2 with hd
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ => hD0 _ _
    have hdc : ∀ l r, f l ≠ 0 → d * β.coord q (b l r) ∈ chartRing R (segreVec y) c := by
      intro l r hl
      have hsplit := Finset.mul_prod_erase Finset.univ (fun p : Fin k × Fin N => D p.1 p.2)
        (Finset.mem_univ (l, r))
      dsimp only at hsplit
      rw [hd, ← hsplit]
      have : D l r * (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * β.coord q (b l r) =
          (∏ p ∈ Finset.univ.erase (l, r), D p.1 p.2) * (D l r * β.coord q (b l r)) := by ring
      rw [this]
      exact mul_mem (prod_mem fun p _ => hDA _ _) (hDc l r hl)
    have hψ : ∀ v ∈ B.lat c, (d • β.coord q) v ∈ chartRing R (segreVec y) c := by
      intro v hv
      rw [LinearMap.smul_apply, smul_eq_mul]
      refine Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem _ Finset.univ f cc hsum hf hcc _ ?_
      intro l
      by_cases hl : f l = 0
      · exact ⟨1, by simp [hl]⟩
      obtain ⟨a', ha', hrep⟩ := (hiff l v).1 ⟨0, by simpa using hv⟩
      obtain ⟨n, hn⟩ := TwistedDualGensSpan.sum_mul_mem_localized _ (hf l) a'
        (fun r => d * β.coord q (b l r)) ha' (fun r => hdc l r hl)
      refine ⟨n, ?_⟩
      have : d * β.coord q v = ∑ r, a' r * (d * β.coord q (b l r)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hrep, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_smul, smul_eq_mul]; ring
      rw [smul_eq_mul, this]
      exact hn
    obtain ⟨u, -, hu⟩ := hφ.generate c hc (d • β.coord q) hψ
    have hmem : d • β.coord q ∈ Submodule.span Ω (Set.range φ) := by
      rw [hu]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)
    have : β.coord q = d⁻¹ • (d • β.coord q) := by rw [smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem
  rw [eq_top_iff, ← β.dualBasis.span_eq, Module.Basis.coe_dualBasis]
  exact Submodule.span_le.2 (by rintro _ ⟨q, rfl⟩; exact key q)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinIntNum
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinIntNum.Statement : Prop :=
  ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (V : Ideal (MRing ι F)) (n : ℕ) (bs : Fin n → K → ℤ),
    intNum F (V.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (bs j)) =
      intNum F V bs

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsJoinDivCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx)

def JoinDivCycle.Statement : Prop :=
  ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι R)) (f : MRing ι R),
    ReciprocityTheory.ChartRestriction.G.Geo.divCycle (P.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx) f) =
      Finsupp.mapDomain (Ideal.map (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar (ι := ι) ptIdx)))
        (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsHsymmShift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def HsymmShift.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (W : Ideal (MRing ι F)), IsMultiProjPrime W →
    ∀ d : ℕ, FieldNumbers.relDim W = (d : WithBot (WithTop ℤ)) →
    ∀ (N : ℕ), 0 < N → ∀ (x : Fin N → K → ℤ) (s : K → ℤ) (r : ℕ) (Y : List (K → ℤ)),
      r + Y.length = d →
      ∑ α ∈ Finset.Nat.antidiagonalTuple N r, intNumL F W (rootList (fun i => x i + s) α ++ Y) =
        ∑ k ∈ Finset.range (r + 1), ((N - 1 + r).choose k : ℤ) *
          ∑ α ∈ Finset.Nat.antidiagonalTuple N (r - k),
            intNumL F W (rootList x α ++ List.replicate k s ++ Y)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair assocDeg assocVar)

def FlagPairJoinLeft.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord z w))) N V,
      IsPull O x (joinCoord z w) E EB → IsPull O x (joinCoord z w) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord z w)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => assocDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => assocDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (assocVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (assocVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsBisTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord IsPull FlagPair midDeg midVar)

def FlagPairJoinRight.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
    [Algebra O Ω] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (z : (Σ k, ι' k) → Ω) (K₂ : Type) [Fintype K₂] (ι₂ : K₂ → Type) [∀ k, Fintype (ι₂ k)]
    (w : (Σ k, ι₂ k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (EF E'F : ChartBundle O (mseg (joinCoord x z)) N V),
    IsPull O x z E EF → IsPull O x z E' E'F → ∀ φ : FlagPair O (joinCoord x z) EF E'F,
    ∀ EB E'B : ChartBundle O (mseg (joinCoord x (joinCoord w z))) N V,
      IsPull O x (joinCoord w z) E EB → IsPull O x (joinCoord w z) E' E'B →
    ∃ ψ : FlagPair O (joinCoord x (joinCoord w z)) EB E'B,
      ψ.Vs = φ.Vs ∧ ψ.gen = φ.gen ∧ ψ.gen' = φ.gen' ∧
      ψ.deg = (fun i => midDeg (K₂ := K₂) (φ.deg i)) ∧
      ψ.deg' = (fun i => midDeg (K₂ := K₂) (φ.deg' i)) ∧
      ψ.f = (fun i => rename (midVar ι₂) (φ.f i)) ∧ ψ.g = (fun i => rename (midVar ι₂) (φ.g i))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def FlagLineSection.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∀ h0 : 0 < N,
      ∃ (bf bg : Option K → ℕ) (f g : MRing (bundleIdx ι M) F),
        IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
        f ∉ projIdeal F y w φ (truncCoord t 1) ∧ g ∉ projIdeal F y w φ (truncCoord t 1) ∧
        (fun o => (bf o : ℤ) - bg o) = zetaDeg - liftDeg (a - b ⟨0, h0⟩) ∧
        ratDiv (projIdeal F y w φ (truncCoord t 1)) f g = 0

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

instance projIdeal.isPrime {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M : ℕ} {E : Type*}
    [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ] (F : Type*) [Field F]
    [Algebra F Ω] (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) : (projIdeal F y w φ t).IsPrime := by
  unfold projIdeal
  exact RingHom.ker_isPrime _

def FlagLineDegree.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E]
      (B : ChartBundle F (segreVec y) N E) (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ),
      IsFlagFrame y B w b →
    ∀ (M : ℕ) (a : K → ℤ) (φ : Fin M → Module.Dual Ω E), IsTwistedDualGens y B a φ →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (t : Fin N → Φ), AlgebraicIndependent Ω t →
    0 < N →
      FieldNumbers.relDeg (Function.Embedding.some : K ↪ Option K)
        (projIdeal F y w φ (truncCoord t 1)) = 1

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx ptCoord)

def JoinPointNumbers.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (r : ℕ) (deg : Fin r → K → ℤ) (H : MvPolynomial (Fin r) ℤ),
    (∀ (b : K → ℤ) (f g : MRing ι O), IsVerticalDivisor (pointIdeal O y) ϖ b f g →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) f)
          (rename (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.liftVar ptIdx) g)) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.ratCyc O (pointIdeal O y) f g)) ∧
    (∀ a : O, a ≠ 0 →
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.fieldNum (IsLocalRing.ResidueField O) (Sum.elim ι ptIdx)) V d
                                (fun j => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.pullDeg (K' := Unit) (deg j)) H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (ReciprocityTheory.ChartRestriction.G.Geo.divCycle
          (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.mcIdeal O (IndefiniteRowSideFullHecke.NumbersDVR.Bundles.joinCoord y (ptCoord (Ω := Ω))))
          (C a))) =
      IndefiniteRowSideFullHecke.NumbersDVR.Bundles.vEval O (fun V => IndefiniteRowSideFullHecke.NumbersDVR.Bundles.polyNum
                                (fun V _ bs => intNum (IsLocalRing.ResidueField O) V bs) V d deg H)
        (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
          (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (pointIdeal O y) (C a))))

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivCycleEqZeroOfFormNotMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem divCycle_nonneg (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> simp

theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dite_eq_right]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dite_eq_right h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinBirationalJoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.Geo (chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord fnField)

section Proof

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] {ι : K → Type} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type}


omit [Fintype K] in
theorem BirationalJoin.segre_ratio_mem_fnField (y : (Σ k, ι k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (c₁ c₂ : ∀ k, ι₂ k) : segreVec w c₁ / segreVec w c₂ ∈ fnField O (joinCoord y w) := by
  unfold segreVec
  rw [← Finset.prod_div_distrib]
  refine Subfield.prod_mem _ fun k _ => ?_
  apply Subfield.subset_closure
  refine Or.inr ⟨⟨Sum.inr k, c₁ k, c₂ k⟩, rfl⟩

theorem BirationalJoin.segreVec_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K)
    (i : ι k) :
    segreVec y (Function.update c k i) = y ⟨k, i⟩ * ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ := by
  unfold segreVec
  have hf : (fun l => y ⟨l, Function.update c k i l⟩) =
      Function.update (fun l => y ⟨l, c l⟩) k (y ⟨k, i⟩) := by
    funext l
    by_cases hl : l = k
    · subst hl
      simp
    · simp [Function.update_of_ne hl]
  rw [hf, Finset.prod_update_of_mem (Finset.mem_univ k)]

theorem BirationalJoin.fnField_le_closure_chartRing (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : segreVec y c ≠ 0) :
    fnField O y ≤ Subfield.closure (chartRing O (segreVec y) c : Set Ω) := by
  classical
  refine Subfield.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | ⟨⟨k, i, j⟩, rfl⟩)
  · exact Subfield.subset_closure (Subalgebra.algebraMap_mem _ a)
  · have hk : y ⟨k, c k⟩ ≠ 0 := Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
    set P := ∏ l ∈ Finset.univ \ {k}, y ⟨l, c l⟩ with hP
    have hcP : segreVec y c = y ⟨k, c k⟩ * P := by
      have h := BirationalJoin.segreVec_update y c k (c k)
      rwa [Function.update_eq_self] at h
    have hP0 : P ≠ 0 := by
      intro h0
      apply hc
      rw [hcP, h0, mul_zero]
    have hmem : ∀ m : ι k, segreVec y (Function.update c k m) / segreVec y c ∈
        Subfield.closure (chartRing O (segreVec y) c : Set Ω) := fun m =>
      Subfield.subset_closure (Algebra.subset_adjoin ⟨Function.update c k m, rfl⟩)
    have key : y ⟨k, i⟩ / y ⟨k, j⟩ = (segreVec y (Function.update c k i) / segreVec y c) /
        (segreVec y (Function.update c k j) / segreVec y c) := by
      rw [div_div_div_cancel_right₀ hc, BirationalJoin.segreVec_update,
        BirationalJoin.segreVec_update, mul_div_mul_right _ _ hP0]
    show y ⟨k, i⟩ / y ⟨k, j⟩ ∈ _
    rw [key]
    exact Subfield.div_mem _ (hmem i) (hmem j)

theorem BirationalJoin.exists_div_of_mem_closure (S : Subalgebra O Ω) {x : Ω}
    (hx : x ∈ Subfield.closure (S : Set Ω)) : ∃ a ∈ S, ∃ b ∈ S, x = a / b := by
  have hS : Subring.closure (S : Set Ω) = S.toSubring := by
    rw [← Subalgebra.coe_toSubring]
    exact Subring.closure_eq _
  obtain ⟨a, ha, b, hb, rfl⟩ := Subfield.mem_closure_iff.mp hx
  rw [hS] at ha hb
  exact ⟨a, ha, b, hb, rfl⟩

end Proof

theorem BirationalJoin.proof : BirationalJoin.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ y K₂ _ ι₂ _ w h c hc c₁ c₂ hc₂
  have hr : segreVec w c₁ / segreVec w c₂ ∈ fnField O y :=
    h ▸ BirationalJoin.segre_ratio_mem_fnField y w c₁ c₂
  obtain ⟨a, ha, b, hb, hab⟩ := BirationalJoin.exists_div_of_mem_closure _
    (BirationalJoin.fnField_le_closure_chartRing y c hc hr)
  by_cases hb0 : b = 0
  · have hw : segreVec w c₁ = 0 := by
      rw [hb0, div_zero, div_eq_zero_iff] at hab
      exact hab.resolve_right hc₂
    exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by rw [hw, zero_mul, zero_mul]⟩
  · exact ⟨a, ha, b, hb, hb0, (div_eq_div_iff hc₂ hb0).mp hab⟩

end GroundTheory.Heights₂.Heights.NumbersDVR
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.WithBotLtOfAddOneLe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

namespace AdditivityInDivisor

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem cycEval_add_cycle {n Z₁ Z₂ : Ideal (MRing ι R) → ℤ} (h₁ : (Function.support Z₁).Finite)
    (h₂ : (Function.support Z₂).Finite) : cycEval n (Z₁ + Z₂) = cycEval n Z₁ + cycEval n Z₂ := by
  unfold cycEval
  rw [← finsum_add_distrib (h₁.subset (Function.support_mul_subset_left _ _))
    (h₂.subset (Function.support_mul_subset_left _ _))]
  exact finsum_congr fun W => by simp [add_mul]

theorem cycEval_add_fn {n n₁ n₂ Z : Ideal (MRing ι R) → ℤ} (hZ : (Function.support Z).Finite)
    (h : ∀ W, Z W ≠ 0 → n W = n₁ W + n₂ W) : cycEval n Z = cycEval n₁ Z + cycEval n₂ Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · simp [hW]
  · rw [h W hW, mul_add]

theorem ratDiv_support_finite {P : Ideal (MRing ι R)} {f g : MRing ι R}
    (hf : (Function.support (divCycle P f)).Finite) (hg : (Function.support (divCycle P g)).Finite) :
    (Function.support (ratDiv P f g)).Finite := by
  refine (hf.union hg).subset fun W hW => ?_
  by_contra h
  simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
  exact hW (by simp [ratDiv, h.1, h.2])

theorem withBot_lt_of_add_one_le {x : WithBot ℕ∞} {n : ℕ} (hx : x + 1 ≤ (n : WithBot ℕ∞)) :
    x < (n : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have e : ((⊤ : ℕ∞) : WithBot ℕ∞) + 1 = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e] at hx
      exact absurd (WithBot.coe_le_coe.mp hx) (by simp)
    | coe m =>
      have h1 : ((m + 1 : ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) := by simpa using hx
      have h2 : m + 1 ≤ n := by exact_mod_cast h1
      have h3 : ((m : ℕ) : WithBot ℕ∞) < ((n : ℕ) : WithBot ℕ∞) := by exact_mod_cast (show m < n by omega)
      simpa using h3

theorem ratDiv_mul_mul (hmul : DivCycleMul.Statement.{u}) {O : Type u} [CommRing O] [IsNoetherianRing O]
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι O)} (hP : P.IsPrime)
    {f₁ g₁ f₂ g₂ : MRing ι O} (hf₁ : f₁ ∉ P) (hf₂ : f₂ ∉ P) (hg₁ : g₁ ∉ P) (hg₂ : g₂ ∉ P) :
    ratDiv P (f₁ * f₂) (g₁ * g₂) = ratDiv P f₁ g₁ + ratDiv P f₂ g₂ := by
  funext W
  simp only [ratDiv, Pi.add_apply, hmul O K ι P f₁ f₂ hP hf₁ hf₂, hmul O K ι P g₁ g₂ hP hg₁ hg₂]
  ring

end AdditivityInDivisor

theorem AdditivityInDivisor.proof (hmul : DivCycleMul.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u})
    (hadd : IntNumAddFirst.Statement.{u}) (hsup : SupSpanMultiHomog.Statement.{u})
    (hmin : MinimalPrimeMultiHomog.Statement.{u}) (hspm : SpecialIdealMultiHomog.Statement.{u})
    (hcor : SpecialIdealCorresp.Statement.{u}) (hqd : SpecialQuotDim.Statement.{u})
    (hdrop : DimStrictDrop.Statement.{u}) : AdditivityInDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b₁ b₂ f₁ g₁ f₂ g₂ hD₁ hD₂ c s hs hsP hsH L
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have rfin : ∀ (Q : Ideal (MRing ι O)) (x y : MRing ι O), (Function.support (ratDiv Q x y)).Finite :=
    fun Q x y => ratDiv_support_finite (hfin O K ι Q x) (hfin O K ι Q y)
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [ratDiv_mul_mul hmul hPp hD₁.num_not_mem hD₂.num_not_mem hD₁.den_not_mem hD₂.den_not_mem]
    exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)
  · unfold cutIdentityRightSide
    refine cycEval_add_fn (hfin O K ι P s) fun W hW => ?_
    obtain ⟨hWp, hPW, -⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
    split_ifs with hϖW
    ·
      have hWmin : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes := by
        unfold divCycle at hW
        split_ifs at hW with h
        · exact h.1
        · exact absurd rfl hW
      have hWh : IsMultiHomogIdeal W :=
        hmin O K ι _ W (hsup O K ι P s c hP.multiProj.multiHomog hs) hWmin
      have hsW : s ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
      have hlt : P < W := lt_of_le_of_ne hPW fun h => hsP (h ▸ hsW)
      have hdim := hdrop (MRing ι O) P W hlt
      rw [hP.dim, ← hqd O ϖ hϖ K ι W hϖW,
        show d + 1 + 1 + Fintype.card K = d + 2 + Fintype.card K by ring] at hdim
      exact hadd _ K ι d (specialIdeal W) (hcor O ϖ hϖ K ι P W hWp hϖW).1 (hspm O K ι W hWh)
        (withBot_lt_of_add_one_le hdim) b₁ b₂ L
    ·
      obtain ⟨hV₁, hV₂⟩ := hsH W hW hϖW
      rw [ratDiv_mul_mul hmul hWp hV₁.num_not_mem hV₂.num_not_mem hV₁.den_not_mem hV₂.den_not_mem]
      exact cycEval_add_cycle (rfin _ _ _) (rfin _ _ _)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
