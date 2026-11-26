module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm

@[expose] public section

section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwtrContOfMem
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem twtr_cont_of_mem (π : CuspSub E n) {ψ : Sm E n} (hψ : ψ ∈ π.V) : Continuous ψ.1 :=
  GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E n ψ (π.cusp ψ hψ).1.level

theorem twtr_integrable (μ : Measure (H E n 0)) [IsLocallyFiniteMeasure μ] {φ : H E n 0 → ℂ} (hφ : IsTestH φ)
    {f : GA E n → ℂ} (hf : Continuous f) (x : GA E n) :
    Integrable (fun y : H E n 0 => φ y * f (x * y.1)) μ := by
  have : BorelSpace (H E n 0) := ⟨rfl⟩
  have : IsFiniteMeasureOnCompacts μ :=
    ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ => μ.finiteAt_nhdsWithin x K⟩
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hφ.1.mul (hf.comp (continuous_const.mul continuous_fst))
  · exact hφ.2.mul_right

end

end DiscreteGroups.T1.G

end
end

section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CutTailC
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped Classical

attribute [local instance] borelH

namespace DiscreteGroups.T1.G

def CutTail2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0)
  (π : CuspSub E n), ThetaFix π → ∀ (ι : Type) [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (H E n 0 → ℂ))
  (T₁ T₂ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (M : Matrix ι ι ℂ) (k₁ k₂ : H E n 0 → ι → Hs (ι := ι) D) (r₀ r₁ ε : ℝ),
  IsTestM Φ₁ → IsTestM Φ₂ → (∀ i j, FinOn D.μ π (Φ₁ i j)) → IsROp D Φ₁ T₁ → IsROp D Φ₂ T₂ →
  IsVecs D Φ₁ Φ₂ T₁ T₂ M k₁ k₂ → 0 ≤ r₀ → 0 ≤ r₁ → 0 < ε → ∃ C'₀ : ℝ, ∀ C' : ℝ, C'₀ ≤ C' → ∃ C : ℝ,
  ∀ (k : ℕ) (U Uπ : Hs (ι := ι) D →L[ℂ] Hs (ι := ι) D) (Φ : Matrix ι ι (H E n 0 → ℂ)), IsTestM Φ →
    IsROp D Φ (T₁ * U * T₂) → IsPiPart D π U Uπ → D4.IsTest2J (trM Φ M) (r₀ + k * r₁) →
    ‖∫ x, lInt D k₁ k₂ (C' * ((1 + k) * (1 + r₀ + r₁))) Uπ x ∂D.ν - ∫ x, lInt0 D k₁ k₂ Uπ x ∂D.ν‖ ≤ C * ‖U‖ * ε ^ k

theorem growth_of_ellipticFormula (hE : D4.EllFormula2J) (hS : SFun) (hD : DomOne) (hK : KerSplit) (hU : UncutHalf)
    (hT : CutTail2) : GrowthPiJ := by
  intro E _ _ _ _ n hn _ _ _ _ μ₁ _ μ₂ _
  obtain ⟨F₁, F₂, D, h₁, h₂, hcut, hmu⟩ := hD E n μ₁ μ₂
  refine ⟨D, hmu, ?_⟩
  intro π hπ ι _ Φ₁ Φ₂ T₁ T₂ M r₀ r₁ ε a1 a2 hfin b1 b2 hr₀ hr₁ hε
  obtain ⟨C₀, hC₀, hell⟩ := hE E n 0
  obtain ⟨k₁, k₂, hv, C, N, hb⟩ := hS E n 0 D ι Φ₁ Φ₂ T₁ T₂ M a1 a2 b1 b2
  obtain ⟨C'₀, hT'⟩ := hT E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ r₀ r₁ ε a1 a2 hfin b1 b2 hv hr₀ hr₁ hε
  obtain ⟨Ct, hCt⟩ := hT' (max C₀ C'₀) (le_max_right _ _)
  have hC'0 : 0 ≤ max C₀ C'₀ := le_trans hC₀ (le_max_left _ _)
  refine ⟨max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct|, N, fun k U Φ t c1 c2 hU1 hU2 c3 ht => ?_⟩
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : 0 ≤ r₀ + k * r₁ := by positivity
  have hg : 1 + (r₀ + k * r₁) ≤ (1 + k) * (1 + r₀ + r₁) := by
    nlinarith [mul_nonneg hk hr₀, mul_nonneg hk hr₁]
  have hτ0 : 0 ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) := by positivity
  have hτC : C₀ * (1 + (r₀ + k * r₁)) ≤ max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁)) :=
    mul_le_mul (le_max_left _ _) hg (by positivity) hC'0
  have e1 : ellSum2 μ₁ μ₂ (trM Φ M) = ∫ x, lInt D k₁ k₂ (max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) U x ∂D.ν := by
    rw [← hell μ₁ μ₂ F₁ F₂ _ _ _ h₁ h₂ c3 hr hτC, ← hcut]
    exact (hb _ hτ0 U).2.2 Φ c1 c2
  obtain ⟨Uπ, hpi, -, hsplit⟩ := hK E n D π ι k₁ k₂ _ C N (fun V => ⟨(hb _ hτ0 V).1, (hb _ hτ0 V).2.1⟩) U hU1 hU2
  obtain ⟨-, hhalf⟩ := hU E n hn D π hπ ι Φ₁ Φ₂ T₁ T₂ M k₁ k₂ a1 a2 hfin b1 b2 hv U Uπ Φ t c1 c2 hpi ht
  have htail := hCt k U Uπ Φ c1 c2 hpi c3
  rw [e1, ← hhalf]
  refine (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add hsplit htail).trans (add_le_add ?_ ?_))
  · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc C * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N
        ≤ |C| * (1 + max C₀ C'₀ * ((1 + k) * (1 + r₀ + r₁))) ^ N :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * ((1 + max C₀ C'₀ * (1 + r₀ + r₁)) * (1 + k)) ^ N := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (abs_nonneg C)
          nlinarith [mul_nonneg hC'0 hk]
      _ = |C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N * (1 + k) ^ N := by rw [mul_pow, mul_assoc]
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (1 + k) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have h1 : Ct ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| := (le_abs_self Ct).trans (le_max_right _ _)
    have h0 : 0 ≤ ‖U‖ * ε ^ k := by positivity
    calc Ct * ‖U‖ * ε ^ k = Ct * (‖U‖ * ε ^ k) := by ring
      _ ≤ max (|C| * (1 + max C₀ C'₀ * (1 + r₀ + r₁)) ^ N) |Ct| * (‖U‖ * ε ^ k) := mul_le_mul_of_nonneg_right h1 h0
      _ = _ := by ring

end DiscreteGroups.T1.G

end
end

section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.TwistSatHolds
section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.CTZeroCut
section -- merged from Development.DiscreteGroups.PiInvariants.CompactSupportTwists.NoPiHk
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def locT (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) : Module.End ℂ (Sm E n) :=
  finRep E n (locGL E n w g)

def FixAt (w : HeightOneSpectrum (𝓞 E)) (f : Sm E n) : Prop := ∀ k ∈ GlobalTheory.LFun.KGL w (n := n), locT w k f = f

def InKgK (w : HeightOneSpectrum (𝓞 E)) (g y : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∃ k₁ ∈ GlobalTheory.LFun.KGL w (n := n), ∃ k₂ ∈ GlobalTheory.LFun.KGL w (n := n), y = k₁ * g * k₂

def IsHk (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (w.adicCompletion E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) :
    Prop :=
  (∀ r ∈ R, InKgK w g r) ∧ ∀ y, InKgK w g y → ∃! r, r ∈ R ∧ r⁻¹ * y ∈ GlobalTheory.LFun.KGL w (n := n)

def hk (w : HeightOneSpectrum (𝓞 E)) (R : Finset (GL (Fin n) (w.adicCompletion E))) : Module.End ℂ (Sm E n) :=
  ∑ r ∈ R, locT w r

end Defs

end DiscreteGroups.T1.G

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.RgJS
open GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def GSat (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ) (φ : Sm E n) : Prop :=
  ∀ w, w ∉ S → FixAt w φ ∧ (B w).card = n ∧ ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, ∀ g : GL (Fin n) (w.adicCompletion E),
    (g : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal (fun i : Fin n => if (i : ℕ) < j then ϖ else 1) →
    ∀ R, IsHk w g R → ∃ m : ℕ, ((hk w R - satEig (qV E w) n (B w) j • (1 : Module.End ℂ (Sm E n))) ^ m) φ = 0

end Defs

def Supp : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (φ : Sm E n), IsAutForm φ →
  φ ≠ 0 → ∀ S B, GSat S B φ →
  ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (σ : ∀ i, CuspSub E (m i)), Nonempty ι ∧ (∀ i, 1 ≤ m i) ∧
    ∀ᶠ w in Filter.cofinite, ∃ Bi : ι → Multiset ℂˣ, (∀ i, (CG.mk (σ i)).HasSat w (Bi i)) ∧ ∑ i, Bi i = B w

end DiscreteGroups.T1.G

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun Formalism.UG GlobalTheory.PRep

namespace DiscreteGroups.T1.G

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem absC_loc (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) (n : ℤ)
    (hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n)) :
    (((Model.absC E u).loc w x : ℂˣ) : ℂ) = Complex.exp (u * (-(n * Real.log (Ideal.absNorm w.asIdeal : ℕ)) : ℝ)) := by
  change Complex.exp (u * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) = _
  rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx]

theorem absC_unrAt (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) : (Model.absC E u).UnrAt w := by
  intro x hx
  apply Units.ext
  rw [absC_loc u w x 0 (by rw [hx]; simp)]
  simp

theorem absC_val (u : ℂ) (w : HeightOneSpectrum (𝓞 E)) :
    (((Model.absC E u).val w : ℂˣ) : ℂ) = ((qV E w : ℕ) : ℂ) ^ (-u) := by
  have hu : Valued.v ((atFin w (unif w) : (w.adicCompletion E)ˣ) : w.adicCompletion E) = WithZero.exp (-(1 : ℤ)) :=
    unif_spec w
  have h := absC_loc u w (atFin w (unif w)) 1 hu
  change (((Model.absC E u).loc w (atFin w (unif w)) : ℂˣ) : ℂ) = _
  rw [h, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.2 (qV_ne_zero w))]
  have e : Complex.log ((qV E w : ℕ) : ℂ) = ((Real.log (Ideal.absNorm w.asIdeal : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]; rfl
  rw [e]
  congr 1
  push_cast
  ring

end DiscreteGroups.T1.G

end
end
