module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocQuot
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocQuot.proof : DegZeroLocQuot.Statement := by
  intro F _ K _ ι P _ 𝒲 h𝒲 x hx

  set φ : MRing ι F →+* FractionRing (MRing ι F ⧸ P) :=
    (algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))).comp (Ideal.Quotient.mk P) with hφ
  have hne : ∀ g : MRing ι F, g ∉ P → φ g ≠ 0 := fun g hg => by
    rw [hφ, RingHom.comp_apply, Ne, IsFractionRing.to_map_eq_zero_iff,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hg
  let Q : FractionRing (MRing ι F ⧸ P) → Prop := fun y =>
    ∃ (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b ∧ IsMultiHomog g b ∧
      g ∉ P ∧ (∀ W ∈ 𝒲, g ∉ W) ∧ y = φ f / φ g
  have key : Q x := by
    refine Algebra.adjoin_induction (p := fun y _ => Q y) ?_ ?_ ?_ ?_ hx
    · rintro y ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
      exact ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩
    · intro c
      refine ⟨0, C c, 1, isWeightedHomogeneous_C _ c, isWeightedHomogeneous_one F _, ?_, ?_, ?_⟩
      · exact (Ideal.ne_top_iff_one P).mp (Ideal.IsPrime.ne_top inferInstance)
      · intro W hW
        exact (Ideal.ne_top_iff_one W).mp (h𝒲 W hW).ne_top
      · rw [map_one, div_one, hφ, RingHom.comp_apply,
          IsScalarTower.algebraMap_apply F (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))]
        rfl
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * g' + g * f', g * g', (hf.mul hg').add (hg.mul hf'), hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_add_div _ _ (hne g hgP) (hne g' hgP'), map_add (f := _), map_mul, map_mul, map_mul]
    · rintro y z - - ⟨b, f, g, hf, hg, hgP, hgW, rfl⟩ ⟨b', f', g', hf', hg', hgP', hgW', rfl⟩
      refine ⟨b + b', f * f', g * g', hf.mul hf', hg.mul hg', ?_, ?_, ?_⟩
      · exact fun h => ((Ideal.IsPrime.mem_or_mem inferInstance h).elim hgP hgP')
      · intro W hW h
        exact ((h𝒲 W hW).mem_or_mem h).elim (hgW W hW) (hgW' W hW)
      · rw [div_mul_div_comm, map_mul, map_mul]
  exact key

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsMChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Chart

variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type*} [Field F]

def chartMonomial [Fintype K] (u : ∀ k, ι k) (b : K → ℕ) : MRing ι F :=
  ∏ k, X ⟨k, u k⟩ ^ b k

def chartMap (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    MRing ι F →ₐ[F] FractionRing (MRing ι F ⧸ P) :=
  aeval fun v => algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (X v)) /
    algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (X ⟨v.1, u v.1⟩))

def chartIdeal (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) : Ideal (MRing ι F) :=
  RingHom.ker (chartMap P u)

instance chartIdeal.isPrime (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k) :
    (chartIdeal P u).IsPrime :=
  RingHom.ker_isPrime _

end Chart

def MChartDehomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (P : Ideal (MRing ι F)) [P.IsPrime] (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
    ∀ (f : MRing ι F) (b : K → ℕ), IsMultiHomog f b →
      chartMap P u f = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P f) /
        algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartHomog.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    (u : ∀ k, ι k) (p : MRing ι F), ∃ (b : K → ℕ) (h : MRing ι F), IsMultiHomog h b ∧
      ∀ (P : Ideal (MRing ι F)) [P.IsPrime], (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
        chartMap P u p = algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P h) /
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P (chartMonomial u b))

def MChartTrdeg.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) [P.IsPrime], IsMultiHomogIdeal P →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ P) →
      Algebra.trdeg F (MRing ι F ⧸ chartIdeal P u) + Fintype.card K = Algebra.trdeg F (MRing ι F ⧸ P)

def MChartLocDim.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι F)) [P.IsPrime] [W.IsPrime], P ≤ W →
    ∀ (u : ∀ k, ι k), (∀ k, (X ⟨k, u k⟩ : MRing ι F) ∉ W) →
      ringKrullDim (degZeroLoc P {W}) =
        ((chartIdeal W u).map (Ideal.Quotient.mk (chartIdeal P u))).height

section Example

end Example

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreFinite.proof : FibreFinite.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _
  have := hP'.isPrime
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
    (P' ⊔ W.map (rename (blockIncl j ι')))).subset ?_
  rintro W' ⟨hW', hPW', hc⟩
  have := hW'.isPrime
  obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hPW' (Ideal.map_le_iff_le_comap.mpr hc.ge))
  have := hQ.1.1
  have hP'Q : P' ≤ Q := le_sup_left.trans hQ.1.2
  suffices Q = W' by rwa [← this]
  by_contra hne
  have hQc : contractPrime j Q = W := le_antisymm (hc ▸ Ideal.comap_mono hQW')
    (Ideal.le_comap_map.trans (Ideal.comap_mono (le_sup_right.trans hQ.1.2)))
  have hne' : P' ≠ Q := by
    rintro rfl
    rw [hQc, hWn] at hPn
    simp only [natCast_withBot_withTop] at hPn
    have := WithTop.coe_inj.mp (WithBot.coe_inj.mp hPn)
    omega
  obtain ⟨f, hfQ, hfP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hP'Q hne')
  obtain ⟨g, hgW, hgQ⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hQW' hne)
  have h1 := ringKrullDim_add_one_le hP'Q hfP hfQ
  have h2 := ringKrullDim_add_one_le hQW' hgQ hgW
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hP'.multiHomog T hq) hP'.relevant
  obtain ⟨E, -, hE⟩ := exists_ringKrullDim_eq
    (fun T _ hq => killBlocks_mem_of_isMultiHomogIdeal hW'.multiHomog T hq) hW'.relevant
  have h3 := ContractRelDimLe.proof F K K' j ι' W' hW'
  rw [hc, hWn, relDim_eq_int hE, natCast_withBot_withTop] at h3
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hP'n
  have h4 : ((E + 1 + 1 : ℕ) : WithBot ℕ∞) ≤ D := by
    rw [← hD]
    rw [hE] at h2
    push_cast
    exact le_trans (by gcongr) h1
  have h3' : (n : ℤ) ≤ E - Fintype.card K' := by exact_mod_cast h3
  have hP'n' : (D : ℤ) - Fintype.card K' = (n + 1 : ℕ) := by exact_mod_cast hP'n
  have h4' : E + 1 + 1 ≤ D := by exact_mod_cast h4
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSemilocalFiniteRank
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Rank

variable {F L₀ L : Type*} [Field F] [Field L₀] [Field L] [Algebra F L₀] [Algebra F L]

theorem isFractionRing_of_div {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    (inj : Function.Injective (algebraMap A K))
    (surj : ∀ z : K, ∃ x y : A, z = algebraMap A K x / algebraMap A K y) : IsFractionRing A K :=
  haveI := (faithfulSMul_iff_algebraMap_injective A K).mpr inj
  IsFractionRing.of_field A K surj

theorem finrank_eq_relfinrank_of_div (φ : L₀ →ₐ[F] L) {K₀ : IntermediateField F L₀}
    {E : IntermediateField F L} (hKE : K₀.map φ ≤ E) {A : Subalgebra F L₀} {B : Subalgebra F L}
    [Algebra A B] (hφ : ∀ a : A, ((algebraMap A B a : B) : L) = φ a) (hA : ∀ a ∈ A, a ∈ K₀)
    (hB : ∀ b ∈ B, b ∈ E) (fracA : ∀ x ∈ K₀, ∃ y ∈ A, ∃ z ∈ A, z ≠ 0 ∧ x = y / z)
    (fracB : ∀ x ∈ E, ∃ y ∈ B, ∃ z ∈ B, z ≠ 0 ∧ x = y / z) :
    Module.finrank A B = IntermediateField.relfinrank (K₀.map φ) E := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hKE]
  set K := K₀.map φ
  set Lf := IntermediateField.extendScalars hKE
  let _ : Algebra A K := (((φ.comp A.val).toRingHom).codRestrict K
    (fun a => show φ a ∈ K from ⟨a, hA a a.2, rfl⟩)).toAlgebra
  let _ : Algebra B Lf := ((B.val.toRingHom).codRestrict Lf (fun b => hB b b.2)).toAlgebra
  let _ : Algebra A Lf := ((algebraMap B Lf).comp (algebraMap A B)).toAlgebra
  have _ : IsScalarTower A B Lf := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have _ : IsScalarTower A K Lf := IsScalarTower.of_algebraMap_eq (fun a => Subtype.ext (hφ a))
  have _ : IsFractionRing A K := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (φ.injective ?_)) ?_
    · exact congrArg Subtype.val h
    · rintro ⟨_, x, hx, rfl⟩
      obtain ⟨y, hy, z, hz, -, rfl⟩ := fracA x hx
      exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext (map_div₀ φ y z)⟩
  have _ : IsFractionRing B Lf := by
    refine isFractionRing_of_div (fun a b h => Subtype.ext (congrArg Subtype.val h :)) ?_
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, -, rfl⟩ := fracB x hx
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, Subtype.ext rfl⟩
  exact (IsFractionRing.finrank_eq A K B Lf).symm

end Rank

theorem mem_homFracDegZero_of_mem_degZeroLoc {K : Type*} [DecidableEq K] {ι : K → Type*}
    {F : Type*} [Field F] (P : Ideal (MRing ι F)) [P.IsPrime] (𝒲 : Set (Ideal (MRing ι F))) :
    ∀ x ∈ degZeroLoc P 𝒲, x ∈ homFracDegZero P := by
  intro x hx
  refine (Algebra.adjoin_le (S := (homFracDegZero P).toSubalgebra) ?_) hx
  rintro _ ⟨b, f, g, hf, hg, hgP, -, rfl⟩
  exact IntermediateField.subset_adjoin _ _ ⟨b, f, g, hf, hg, hgP, rfl⟩

theorem SemilocalFiniteRank.proof (h1 : FibreFinite.Statement.{u})
    (h2 : SemilocalFinite.Statement.{u}) (h3 : DegZeroLocFrac.Statement.{u}) :
    SemilocalFiniteRank.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hd' hd W hW hdW hle
  have := hP'.isPrime
  have hfin := h1 F K K' j ι' P' hP' n hd' hd W hW hdW hle
  have inj : Function.Injective (algebraMap (degZeroLoc (contractPrime j P') {W})
      (degZeroLoc P' (fibrePrimes j P' W))) := by
    intro a b hab
    apply Subtype.ext
    apply (contractFracMap j P').toRingHom.injective
    have := congrArg Subtype.val hab
    rwa [degZeroLoc.algebraMap_contract_coe, degZeroLoc.algebraMap_contract_coe] at this
  refine ⟨h2 F K K' j ι' P' hP' n hd' hd W hW hdW hle, ⟨fun r hr x y hxy => ?_⟩, ?_⟩
  · have hr0 : algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W)) r ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap (degZeroLoc (contractPrime j P') {W})
        (degZeroLoc P' (fibrePrimes j P' W))), inj.eq_iff]
      exact hr.ne_zero
    simp only [Algebra.smul_def] at hxy
    exact mul_left_cancel₀ hr0 hxy
  · refine finrank_eq_relfinrank_of_div (contractFracMap j P') (map_homFracDegZero_le j ι' P')
      (degZeroLoc.algebraMap_contract_coe j P' W)
      (mem_homFracDegZero_of_mem_degZeroLoc _ _) (mem_homFracDegZero_of_mem_degZeroLoc _ _) ?_ ?_
    · intro x hx
      refine h3 F K (fun k => ι' (j k)) (contractPrime j P')
        (isMultiProjPrime_contractPrime _ _ hP') {W} (Set.finite_singleton W) ?_ x hx
      intro W₁ hW₁
      rw [Set.mem_singleton_iff.mp hW₁]
      exact hW
    · exact h3 F K' ι' P' hP' (fibrePrimes j P' W) hfin (fun W' hW' => hW'.1)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocalRing
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem ringKrullDim_eq_of_relDim {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    {F : Type u} [Field F] {Q : Ideal (MRing ι F)} {m : ℕ} (h : relDim Q = (m : ℕ)) :
    ringKrullDim (MRing ι F ⧸ Q) = ((m + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  have hm : ((m : ℕ) : WithBot (WithTop ℤ)) = (((m : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) := rfl
  unfold relDim at h
  rw [hm] at h
  cases hd : ringKrullDim (MRing ι F ⧸ Q) with
  | bot =>
    rw [hd] at h
    exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      exact absurd h (WithTop.top_ne_coe)
    | coe D =>
      rw [hd] at h
      simp only [WithBot.map_coe, WithBot.coe_inj] at h
      change (((D : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) = ((m : ℤ) : WithTop ℤ) at h
      have h := WithTop.coe_inj.mp h
      have : D = m + Fintype.card K := by omega
      rw [this]
      rfl

theorem DegZeroLocalRing.proof (h1 : DegZeroLocLocal.Statement.{u})
    (h2 : DegZeroLocNoetherian.Statement.{u}) (h3 : DegZeroLocDim.Statement.{u}) :
    DegZeroLocalRing.Statement.{u} := by
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  refine ⟨⟨h2 F K ι P hP W hW hPW, h1 F K ι P hP W hW hPW⟩, fun n hn1 hn => ?_⟩
  have e := h3 F K ι P hP W hW hPW
  rw [ringKrullDim_eq_of_relDim hn1, ringKrullDim_eq_of_relDim hn] at e
  revert e
  generalize ringKrullDim (degZeroLoc P {W}) = d
  intro e
  cases d with
  | bot =>
    rw [WithBot.bot_add] at e
    exact absurd e WithBot.bot_ne_coe
  | coe d =>
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj] at e
    induction d using ENat.recTopCoe with
    | top =>
      rw [top_add] at e
      exact absurd e.symm (ENat.natCast_ne_top _)
    | coe d =>
      rw [← Nat.cast_add, Nat.cast_inj] at e
      have : d = 1 := by omega
      rw [this]
      rfl

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocLocalize
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocLocalize.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Finite → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ W ∈ 𝒲, ∀ y ∈ degZeroLoc P {W}, ∃ b ∈ degZeroLoc P 𝒲, ∃ s ∈ degZeroLoc P 𝒲,
      (∃ t ∈ degZeroLoc P {W}, s * t = 1) ∧ y * s = b

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarNumerator
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarNumerator.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ p : MvPolynomial K (degZeroLoc P {W}),
      ∃ (b : K → ℕ) (g : MRing ι F) (h : (K →₀ ℕ) → MRing ι F),
        IsMultiHomog g b ∧ g ∉ W ∧ (∀ d, IsMultiHomog (h d) b) ∧
        (∀ d, ((p.coeff d : degZeroLoc P {W}) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P (h d)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)) ∧
        ((coneVarMap P W hPW v p : coneLocal P W hPW) : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P))
              (Ideal.Quotient.mk P (∑ d ∈ p.support, h d * ∏ k, (X ⟨k, v k⟩ : MRing ι F) ^ d k)) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PFibreRelDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR PFContracted

noncomputable section

universe u

theorem FibreRelDim.proof : FibreRelDim.Statement.{u} := by
  intro F _ K K' _ _ _ _ j ι' _ P' hP' n hP'n hPn W _ hWn _ W' hW'
  obtain ⟨hW'm, hPW', hcW'⟩ := hW'
  have := hP'.isPrime
  have := hW'm.isPrime

  have hge : ((n : ℕ) : WithBot (WithTop ℤ)) ≤ relDim W' := by
    rw [← hWn, ← hcW']
    exact ContractRelDimLe.proof F K K' j ι' W' hW'm

  have hne : ¬ W' ≤ P' := by
    intro hle
    have heq : W' = P' := le_antisymm hle hPW'
    rw [heq] at hcW'
    rw [hcW', hWn] at hPn
    have := congrArg (fun x : WithBot (WithTop ℤ) => x) hPn
    rw [natCast_withBot_withTop, natCast_withBot_withTop] at this
    have h2 := WithTop.coe_injective (WithBot.coe_injective this)
    omega
  obtain ⟨f, hfW', hfP'⟩ := Set.not_subset.mp hne
  have hstab : ∀ {Q : Ideal (MRing ι' F)}, IsMultiProjPrime Q →
      ∀ (T : Finset K') (q : MRing ι' F), q ∈ Q → killBlocks T q ∈ Q :=
    fun hQ T _ hq => killBlocks_mem_of_isMultiHomogIdeal hQ.multiHomog T hq
  obtain ⟨D', -, hD'⟩ := exists_ringKrullDim_eq (hstab hP') hP'.relevant
  obtain ⟨D, -, hD⟩ := exists_ringKrullDim_eq (hstab hW'm) hW'm.relevant
  have hstep := ringKrullDim_add_one_le hPW' hfP' hfW'
  rw [hD, hD'] at hstep
  have hlt : D + 1 ≤ D' := by exact_mod_cast hstep
  rw [relDim_eq_int hD', natCast_withBot_withTop] at hP'n
  have hP'z := WithTop.coe_injective (WithBot.coe_injective hP'n)
  rw [relDim_eq_int hD, natCast_withBot_withTop] at hge ⊢
  have hgez : (n : ℤ) ≤ (D : ℤ) - Fintype.card K' :=
    WithTop.coe_le_coe.mp (WithBot.coe_le_coe.mp hge)
  congr 2
  push_cast at hP'z
  omega

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PDegZeroLocFrac
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

theorem DegZeroLocFrac.proof : DegZeroLocFrac.Statement.{u} := by
  intro F _ K _ _ ι _ P hP 𝒲 h𝒲 h𝒲P
  have := hP.isPrime
  intro x hx

  let E : IntermediateField F (FractionRing (MRing ι F ⧸ P)) :=
    { carrier := {x | ∃ y ∈ degZeroLoc P 𝒲, ∃ z ∈ degZeroLoc P 𝒲, z ≠ 0 ∧ x = y / z}
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * y₂, Subalgebra.mul_mem _ hy₁ hy₂, z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂,
          mul_ne_zero hz₁0 hz₂0, by rw [div_mul_div_comm]⟩
      add_mem' := by
        rintro _ _ ⟨y₁, hy₁, z₁, hz₁, hz₁0, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, hz₂0, rfl⟩
        exact ⟨y₁ * z₂ + z₁ * y₂,
          Subalgebra.add_mem _ (Subalgebra.mul_mem _ hy₁ hz₂) (Subalgebra.mul_mem _ hz₁ hy₂),
          z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_ne_zero hz₁0 hz₂0,
          by rw [div_add_div _ _ hz₁0 hz₂0]⟩
      algebraMap_mem' := fun c => ⟨algebraMap F _ c, Subalgebra.algebraMap_mem _ c, 1,
        Subalgebra.one_mem _, one_ne_zero, (div_one _).symm⟩
      inv_mem' := by
        rintro _ ⟨y, hy, z, hz, hz0, rfl⟩
        by_cases hy0 : y = 0
        · exact ⟨0, Subalgebra.zero_mem _, 1, Subalgebra.one_mem _, one_ne_zero, by simp [hy0]⟩
        · exact ⟨z, hz, y, hy, hy0, by rw [inv_div]⟩ }
  suffices hle : homFracDegZero P ≤ E from hle hx
  unfold homFracDegZero
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩

  obtain ⟨e, h, hh, hbe, hhS⟩ := exists_form_avoid_primes (insert P h𝒲.toFinset)
    (fun W hW => by
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact ⟨hP.isPrime, hP.multiHomog, hP.relevant⟩
      · have hW' := h𝒲P W (h𝒲.mem_toFinset.mp hW)
        exact ⟨hW'.isPrime, hW'.multiHomog, hW'.relevant⟩) b
  have hhP : h ∉ P := hhS P (Finset.mem_insert_self _ _)
  have hh𝒲 : ∀ W ∈ 𝒲, h ∉ W := fun W hW =>
    hhS W (Finset.mem_insert_of_mem (h𝒲.mem_toFinset.mpr hW))

  obtain ⟨m, hm, hmP⟩ := exists_form_not_mem_of_isRelevant (H := P) hP.relevant (e - b)
  have hfm : IsMultiHomog (f * m) e := by
    have := IsWeightedHomogeneous.mul hf hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hgm : IsMultiHomog (g * m) e := by
    have := IsWeightedHomogeneous.mul hg hm
    rwa [add_tsub_cancel_of_le hbe] at this
  have hq0 : ∀ a : MRing ι F, a ∉ P →
      algebraMap (MRing ι F ⧸ P) (FractionRing (MRing ι F ⧸ P)) (Ideal.Quotient.mk P a) ≠ 0 :=
    fun a ha => by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact ha
  refine ⟨_, div_mem_degZeroLoc P 𝒲 hfm hh hhP hh𝒲, _, div_mem_degZeroLoc P 𝒲 hgm hh hhP hh𝒲,
    div_ne_zero (hq0 _ fun h' => (hP.isPrime.mem_or_mem h').elim hgP hmP) (hq0 _ hhP), ?_⟩
  simp only [map_mul]
  rw [div_div_div_cancel_right₀ (hq0 _ hhP), mul_div_mul_right _ _ (hq0 _ hmP)]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFunctionFieldFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def FunctionFieldFinite.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P'), relDim (contractPrime j P') = relDim P' →
      haveI := hP'.isPrime
      relDeg j P' ≠ 0

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocUnits
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocUnits.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (𝒲 : Set (Ideal (MRing ι F))), 𝒲.Nonempty → (∀ W ∈ 𝒲, IsMultiProjPrime W ∧ P ≤ W) →
    haveI := hP.isPrime
    ∀ x ∈ degZeroLoc P 𝒲,
      (∃ y ∈ degZeroLoc P 𝒲, x * y = 1) ↔ ∀ W ∈ 𝒲, ∃ y ∈ degZeroLoc P {W}, x * y = 1

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarInj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarInj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    Function.Injective (coneVarMap P W hPW v)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarUnit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarUnit.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ (p : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ), IsUnit (p.coeff e) →
      IsUnit (coneVarMap P W hPW v p)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsConeVarSurj
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def ConeVarSurj.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (P : Ideal (MRing ι F)) (hP : IsMultiProjPrime P)
    (W : Ideal (MRing ι F)) (hW : IsMultiProjPrime W) (hPW : P ≤ W) (v : ∀ k, ι k),
    (∀ k, (X ⟨k, v k⟩ : MRing ι F) ∉ W) →
    haveI := hP.isPrime
    haveI := hW.isPrime
    ∀ z : coneLocal P W hPW, ∃ (p q : MvPolynomial K (degZeroLoc P {W})) (e : K →₀ ℕ),
      IsUnit (q.coeff e) ∧ z * coneVarMap P W hPW v q = coneVarMap P W hPW v p

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegZeroLocResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

def DegZeroLocResidue.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K : Type) [DecidableEq K] (ι : K → Type) (P : Ideal (MRing ι F))
    [P.IsPrime] (W : Ideal (MRing ι F)) [W.IsPrime], P ≤ W →
    ∃ ρ : degZeroLoc P {W} →+* FractionRing (MRing ι F ⧸ W),
      (∀ (x : degZeroLoc P {W}) (b : K → ℕ) (f g : MRing ι F), IsMultiHomog f b →
        IsMultiHomog g b → g ∉ W →
        (x : FractionRing (MRing ι F ⧸ P)) =
          algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P f) /
            algebraMap (MRing ι F ⧸ P) _ (Ideal.Quotient.mk P g) →
        ρ x = algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W f) /
            algebraMap (MRing ι F ⧸ W) _ (Ideal.Quotient.mk W g)) ∧
      (∀ x : degZeroLoc P {W},
        ρ x = 0 ↔ ¬ ∃ y ∈ degZeroLoc P {W}, (x : FractionRing (MRing ι F ⧸ P)) * y = 1) ∧
      ∀ z : FractionRing (MRing ι F ⧸ W), z ∈ homFracDegZero W ↔ ∃ x, ρ x = z

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PConeLocalFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR IsLocalRing

noncomputable section

universe u


set_option maxHeartbeats 400000 in
theorem ConeLocalFlat.proof (h : ConePolyLocalization.Statement.{u}) : ConeLocalFlat.Statement.{u} := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro F _ K _ _ ι _ P hP W hW hPW
  have := hP.isPrime
  have := hW.isPrime
  choose v hv using hW.relevant
  obtain ⟨hA, hloc⟩ := h F K ι P hP W hW hPW v hv
  let _ := (coneVarMap P W hPW v).toRingHom.toAlgebra
  have := isPrime_map_C_mvPolynomial K (maximalIdeal (degZeroLoc P {W}))
  have : IsScalarTower (degZeroLoc P {W}) (MvPolynomial K (degZeroLoc P {W})) (coneLocal P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocal P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocal P W hPW)
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _)).primeCompl
    exact Module.Flat.trans _ (MvPolynomial K (degZeroLoc P {W})) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (degZeroLoc P {W})).map (C : degZeroLoc P {W} →+* MvPolynomial K _))
      (coneLocal P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsSemilocalMaxIdeals
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

abbrev degZeroLoc.algebraOfSubset {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
    (P : Ideal (MRing ι F)) [P.IsPrime] {𝒲₁ 𝒲₂ : Set (Ideal (MRing ι F))} (h𝒲 : 𝒲₁ ⊆ 𝒲₂) :
    Algebra (degZeroLoc P 𝒲₂) (degZeroLoc P 𝒲₁) :=
  (Subalgebra.inclusion (degZeroLoc_anti P h𝒲)).toRingHom.toAlgebra


set_option synthInstance.maxHeartbeats 100000 in
set_option synthInstance.maxHeartbeats 400000 in
def SemilocalMaxIdeals.Statement : Prop :=
  ∀ (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
    [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι' F)) (hP' : IsMultiProjPrime P') (n : ℕ), relDim P' = (n + 1 : ℕ) →
    relDim (contractPrime j P') = (n + 1 : ℕ) →
    ∀ W : Ideal (MRing (fun k => ι' (j k)) F), IsMultiProjPrime W → relDim W = (n : ℕ) →
    contractPrime j P' ≤ W →
      haveI := hP'.isPrime
      ∃ (𝔪 : fibrePrimes j P' W → Ideal (degZeroLoc P' (fibrePrimes j P' W)))
        (h𝔪 : ∀ W', (𝔪 W').IsMaximal),
        Function.Injective 𝔪 ∧
        (∀ M : Ideal (degZeroLoc P' (fibrePrimes j P' W)), M.IsMaximal → ∃ W', M = 𝔪 W') ∧
        ∀ W' : fibrePrimes j P' W,
          (haveI := (h𝔪 W').isPrime
           letI := degZeroLoc.algebraOfSubset P' (Set.singleton_subset_iff.mpr W'.2)
           IsLocalization.AtPrime (degZeroLoc P' {W'.1}) (𝔪 W')) ∧
          haveI := W'.2.1.isPrime
          Module.length (degZeroLoc (contractPrime j P') {W})
              (degZeroLoc P' (fibrePrimes j P' W) ⧸ 𝔪 W') = (relDeg j W'.1 : ℕ∞)

end

end GroundTheory.Heights₂.Heights.FieldNumbers
end
