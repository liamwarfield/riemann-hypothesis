module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperCutObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def StepThree.OnW.Gen.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (T : StepData k x), (∀ e ≤ T.d, VeryAmpleNefPlusAmple.InDim.{u, w} k e) →
    ∀ pp ∈ T.J.minimalPrimes, ∃ c₀ : ℤ, ∀ (b : ℕ) (c : ℤ), 1 ≤ b → c₀ ≤ c → ∀ I : Chart x,
      ((T.L.pow b).twist (twistSys k x c)).sub I ≤
        Submodule.span (chartRing k x I) {z | ∃ s : Chart x → Ω, (∀ I', s I' ∈ ((T.L.pow b).twist (twistSys k x c)).sub I') ∧
          (∀ I₁ I₂ : Chart x, I₁.1 ⊆ I₂.1 → s I₁ - s I₂ ∈ (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I₂) ∧ z = s I} ⊔
        (((T.L.pow b).twist (twistSys k x c)).twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionMulInjSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SectionMulInj.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp →
    ∀ (D M : LineBundle k x) (s : Ω), (∃ f ∈ zeroIdeal D.toSubSystem s, f ∉ pp) →
    ∀ (I : Chart x), ∀ y ∈ M.sub I,
      s * y ∈ ((M.toSubSystem.twist D.toSubSystem).twist (idealSys x pp)).sub I →
      y ∈ (M.toSubSystem.twist (idealSys x pp)).sub I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperHyperplane.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp → ∀ a : ℤ,
    ∃ (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp ≤ qq m ∧
        (X i : Poly k N) ∈ qq m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L n (c + 1) - pieceChar k pp a L n c = ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperDevissageSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperDevissage.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubFamily k x E), (∀ I, (F.sub I).FG) →
    ∃ (r : ℕ) (pp : Fin r → Ideal (Poly k N)) (a : Fin r → ℤ),
      (∀ m, (pp m).IsPrime ∧ (∀ f ∈ pp m, ∀ d : ℕ, homogeneousComponent d f ∈ pp m) ∧
        primeOf (S := k) x ≤ pp m) ∧
      ∀ (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
        eulerChar k ((F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c)) =
          ∑ m, pieceChar k (pp m) (a m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperSectionSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SnapperSection.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → (∃ i, (X i : Poly k N) ∉ pp) →
    ∀ (t : ℕ) (L : Fin t → LineBundle k x) (j : Fin t) (a : ℤ),
    ∃ (μ : ℤ) (r : ℕ) (qq : Fin r → Ideal (Poly k N)) (b : Fin r → ℤ),
      (∀ m, (qq m).IsPrime ∧ (∀ f ∈ qq m, ∀ d : ℕ, homogeneousComponent d f ∈ qq m) ∧ pp < qq m) ∧
      ∀ (n : Fin t → ℕ) (c : ℤ),
        pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ) - pieceChar k pp a L n c =
          ∑ m, pieceChar k (qq m) (b m) L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem twistMul_twist_twistMul {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
    {x : Fin (N + 1) → Ω} (M : SubSystem S x Ω) (a a' : ℕ) (c c' : ℤ) :
    (twistMul M a c).twist (twistMul M a' c') = twistMul M (a + a') (c + c') := by
  refine SubSystem.ext_sub fun I => ?_
  rw [SubSystem.twist_sub_eq_mul_of_line, twistMul_sub, twistMul_sub, twistMul_sub, pow_add,
    ← twistSys_sub_mul]
  ring

theorem TwistAlg.proof : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  rw [pow_twistMul, pow_twistMul, pow_twistMul, twistMul_twist_twistMul]
  congr 1
  · ring
  · push_cast
    linear_combination (b₁ : ℤ) * h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Filt.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (M₁ M₂ : FinGradedSub (S := S) (x := x) E), (∀ c, M₂.piece c ≤ M₁.piece c) →
    ∀ J : Ideal (Poly S N), (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ),
      ∀ z ∈ M₁.piece a, aeval x f • z ∈ M₂.piece (a + e)) →
    ∃ (n : ℕ) (Nf : Fin (n + 1) → FinGradedSub (S := S) (x := x) E) (g : Fin n → E) (deg : Fin n → ℤ)
      (pr : Fin n → Ideal (Poly S N)),
      Nf 0 = M₂ ∧ Nf (Fin.last n) = M₁ ∧
      ∀ k : Fin n, (pr k).IsPrime ∧ (∀ p ∈ pr k, ∀ d : ℕ, homogeneousComponent d p ∈ pr k) ∧
        primeOf (S := S) x ≤ pr k ∧
        (∀ (f : Poly S N) (e : ℕ), f ∈ J → f.IsHomogeneous e → f ∈ pr k) ∧
        g k ∈ (Nf k.succ).piece (deg k) ∧
        (∀ c, (Nf k.succ).piece c = (Nf k.castSucc).piece c ⊔ Submodule.span S
          {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ deg k + d = c ∧ z = aeval x f • g k}) ∧
        ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d →
          (f ∈ pr k ↔ aeval x f • g k ∈ (Nf k.castSucc).piece (deg k + d))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperQuotIsoSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w v'

section Defs

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

structure QuotIso {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    {E' : Type v'} [AddCommGroup E'] [Module Ω E'] [Module S E'] [IsScalarTower S Ω E']
    (F₁ F₂ : SubSystem S x E) (G₁ G₂ : SubSystem S x E') where

  equiv : ∀ I : Chart x,
    (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) ≃ₗ[S] (G₁.sub I ⧸ SubSystem.quotSub G₁ G₂ I)

  comm : ∀ (I J : Chart x) (h : I.1 ⊆ J.1) (y : F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I),
    equiv J (SubSystem.quotRes F₁ F₂ I J h y) = SubSystem.quotRes G₁ G₂ I J h (equiv I y)

end Defs

def SnapperQuotIso.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (E' : Type v') [AddCommGroup E'] [Module Ω E'] [Module k E'] [IsScalarTower k Ω E']
    (F₁ F₂ : SubSystem k x E) (G₁ G₂ : SubSystem k x E'), QuotIso F₁ F₂ G₁ G₂ →
    eulerCharQuot k F₁ F₂ = eulerCharQuot k G₁ G₂

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem SectionCount.proof (hT : SectionCount.Top.Statement.{u, w})
    (hD : SectionCount.Drop.Statement.{u, w}) : SectionCount.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb b hZ hN hb
  obtain ⟨C₁, h₁⟩ := hT k Ω N x d Nb hZ hN
  obtain ⟨C₂, h₂⟩ := hD k Ω N x d Nb b hZ hN hb
  refine ⟨C₁ + C₂, ?_⟩
  filter_upwards [h₁, h₂, eventually_ge_atTop 1] with n hn₁ hn₂ hn
  set f : ℕ → ℝ := fun i =>
    (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) with hf
  set Y : ℝ := (interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) : ℝ) with hY
  set X : ℝ := (interNum (primeOf (S := k) x) (Fin.cons (α := fun _ => SubSystem k x Ω)
    (twistSys k x (b : ℤ)) (fun _ : Fin d => Nb.toSubSystem)) : ℝ) with hX
  have h0 : f 0 = (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) :=
    congrArg (fun m : ℤ => (Module.finrank k (twistMul Nb.toSubSystem n m).secs : ℝ)) (by simp)
  have htel : f 0 - f n = ∑ i ∈ Finset.range n, (f i - f (i + 1)) := by
    rw [Finset.sum_range_sub']
  have hsum : ∑ i ∈ Finset.range n, (f i - f (i + 1)) ≤
      ∑ _i ∈ Finset.range n, (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) :=
    Finset.sum_le_sum fun i hi => hn₂ i (Finset.mem_range.mp hi)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : ((d + 1).factorial : ℝ) = ((d : ℝ) + 1) * (d.factorial : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hdf : (0 : ℝ) < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have key : (n : ℝ) * (X * (n : ℝ) ^ d / (d.factorial : ℝ) + C₂ * (n : ℝ) ^ d / n) =
      ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) + C₂ * (n : ℝ) ^ d := by
    rw [hfac]; field_simp; ring
  rw [key] at hsum
  rw [← h0] at hn₁
  have hgoal : f n = (Module.finrank k (twistMul Nb.toSubSystem n (-((n : ℤ) * b))).secs : ℝ) := rfl
  rw [← hgoal]
  push_cast
  have e1 : (Y - ((d : ℝ) + 1) * X) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) =
      Y * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) -
        ((d : ℝ) + 1) * X * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) := by ring
  rw [e1]
  linarith

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoPieceSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def StepTwo.Piece.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    [IsScalarTower S Ω E] (N₀ N₁ : FinGradedSub (S := S) (x := x) E) (g : E) (e : ℤ)
    (pp : Ideal (Poly S N)), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → g ∈ N₁.piece e →
    (∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g}) →
    (∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) →
    ∀ (Q : LineBundle S x) (c : ℤ),
      ((∃ j, (X j : Poly S N) ∉ pp) →
        Subsingleton (SubSystem.quotH (Q.twist (twistSys S x (c - e)))
          ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) 1)) →
      Subsingleton (SubSystem.quotH ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c)))
        ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c))) 1)

section Hypotheses

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


variable (S x E) in
def FinGradedSub.zero : FinGradedSub (S := S) (x := x) E where
  piece _ := ⊥
  smul_mem _ _ _ m _ hm := by
    rw [Submodule.mem_bot] at hm ⊢
    rw [hm, smul_zero]
  fg := ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun _ => bot_le⟩

variable (k : Type u) [Field k]

end Hypotheses

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PQuotSectionsFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

attribute [local instance] MvPolynomial.gradedAlgebra

theorem QuotSectionsFinite.proof (hE : Extension.Statement.{u, w, w})
    (hI : IdealTwistFamily.Statement.{u, w}) (hT : TildeFinite.Statement.{u, w})
    (hQ : QuotientH0Finite.Statement.{u, w, w}) : QuotSectionsFinite.Statement.{u, w} := by
  intro k _ Ω _ _ N x Q J

  let J' : Ideal (Poly k N) := Ideal.span {f | f ∈ J ∧ ∃ e, f.IsHomogeneous e}
  have hJ'hom : ∀ p ∈ J', ∀ d : ℕ, homogeneousComponent d p ∈ J' := by
    have h : J'.IsHomogeneous (homogeneousSubmodule (Fin (N + 1)) k) :=
      Ideal.homogeneous_span _ _ fun f hf =>
        ⟨_, (mem_homogeneousSubmodule _ f).mpr hf.2.choose_spec⟩
    exact fun p hp d => homogeneousComponent_mem_of_mem h hp d
  have hforms : ∀ (f : Poly k N) (e : ℕ), f.IsHomogeneous e → (f ∈ J ↔ f ∈ J') := fun f e hf =>
    ⟨fun h => Ideal.subset_span ⟨h, e, hf⟩, fun h => (show J' ≤ J from Ideal.span_le.mpr (by
      intro g hg
      exact hg.1)) h⟩
  have hsys : idealSys x J = idealSys x J' := SubSystem.ext_sub fun I => by
    change idealMod J I = idealMod J' I
    unfold idealMod
    congr 1
    ext a
    constructor <;> rintro ⟨f, s, e, hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mp hf, hs, hfe, hse, rfl⟩
    · exact ⟨f, s, e, (hforms f e hfe).mpr hf, hs, hfe, hse, rfl⟩

  obtain ⟨F, hF, hFfg⟩ := hI k Ω N x Q J' hJ'hom
  obtain ⟨M, -, hM⟩ := hE k Ω N x Ω Q.toSubFamily Q.fg
  obtain ⟨M', -, hM'⟩ := hE k Ω N x Ω F hFfg
  have h0 : M.tildeSys 0 = Q.toSubSystem := SubSystem.ext_sub hM
  have h1 : M'.tildeSys 0 = Q.toSubSystem.twist (idealSys x J) := by
    rw [hsys, ← hF]
    exact SubSystem.ext_sub hM'

  have hle : ∀ I, (Q.toSubSystem.twist (idealSys x J)).sub I ≤ Q.toSubSystem.sub I := by
    intro I
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    refine Submodule.span_induction (p := fun q _ => q • y ∈ Q.sub I) ?_ ?_ ?_ ?_ hq
    · rintro _ ⟨f, s, e, _, hs, hf, hse, rfl⟩
      exact (Q.sub I).smul_mem ⟨_, ⟨f, s, e, hs, hf, hse, rfl⟩⟩ hy
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq'; rw [smul_assoc]; exact Submodule.smul_mem _ a hq'
  have hH0 : Module.Finite k (Q.toSubSystem.H 0) := by
    rw [← h0]; exact hT k Ω N x M 0 0
  have hH1 : Module.Finite k ((Q.toSubSystem.twist (idealSys x J)).H 1) := by
    rw [← h1]; exact hT k Ω N x M' 1 0
  exact hQ k Ω N x Ω Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) hle hH0 hH1

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem quotH_zero_subsingleton_of_irrelevant (F : SubSystem S x Ω) (pp : Ideal (Poly S N))
    (hpp : ∀ i, (X i : Poly S N) ∈ pp) :
    Subsingleton (SubSystem.quotH F (F.twist (idealSys x pp)) 0) := by
  have hsub : ∀ I : Chart x,
      Subsingleton (F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) := by
    intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
    refine ⟨fun a b => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [Submodule.Quotient.eq]
    change ((a - b : F.sub I) : Ω) ∈ (F.twist (idealSys x pp)).sub I
    rw [SubSystem.twist_sub_eq_mul_of_line]
    have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
      Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
        isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
    simpa using Submodule.mul_mem_mul h1 (a - b).2
  have hC : Subsingleton (Cech.Cochain (fun I : Chart x =>
      F.sub I ⧸ SubSystem.quotSub F (F.twist (idealSys x pp)) I) 0) := by
    unfold Cech.Cochain
    exact ⟨fun a b => funext fun I => (hsub I.1).elim _ _⟩
  unfold SubSystem.quotH Cech.H
  infer_instance

end

theorem SectionCount.Drop.Filt.Finite.proof
    (hRQ : PrimeFiltration.RestrictQuot.Statement.{u, w})
    (hH0 : CechZerothCohomologySections.Statement.{u, w, w})
    (hFS : FiniteSections.Statement.{u, w}) :
    SectionCount.Drop.Filt.Finite.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x Q pp c hpp hhom hle
  by_cases hirr : ∀ i, (X i : Poly S N) ∈ pp
  · have := quotH_zero_subsingleton_of_irrelevant (Q.twist (twistSys S x c)) pp hirr
    infer_instance
  push Not at hirr
  obtain ⟨j, hj'⟩ := hirr
  have hj : x j ≠ 0 := fun h0 => hj' (hle (by
    rw [mem_primeOf_of_isHomogeneous x (isHomogeneous_X S j), aeval_X, h0]))
  have hPtj := PrimeFiltration.Point.proof S Ω N x pp hpp hhom hle j hj hj'

  obtain ⟨K', _, _, ψ, hker⟩ : ∃ (K' : Type w) (_ : Field K') (_ : Algebra S K')
      (ψ : chartRing S x (singleChart hj) →ₐ[S] K'), RingHom.ker ψ = chartPrime pp hj := by
    have : (chartPrime pp hj).IsPrime := hPtj.1
    have : IsDomain (chartRing S x (singleChart hj) ⧸ chartPrime pp hj) := Ideal.Quotient.isDomain _
    refine ⟨FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj), inferInstance, inferInstance,
      (IsScalarTower.toAlgHom S _ _).comp (Ideal.Quotient.mkₐ S (chartPrime pp hj)), ?_⟩
    ext a
    rw [RingHom.mem_ker]
    change algebraMap _ (FractionRing (chartRing S x (singleChart hj) ⧸ chartPrime pp hj))
      (Ideal.Quotient.mk (chartPrime pp hj) a) = 0 ↔ _
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hxy : ∀ i, ψ (ratio hj i) ≠ 0 → x i ≠ 0 := by
    intro i hi h0
    apply hi
    have : ratio (S := S) hj i = 0 := Subtype.ext (show x i / x j = 0 by rw [h0, zero_div])
    rw [this, map_zero]
  have hy0 : (fun i => ψ (ratio hj i)) ≠ 0 := by
    intro h0
    have h1 := congrFun h0 j
    rw [ratio_self hj ψ] at h1
    exact one_ne_zero h1

  obtain ⟨Q', r, hr⟩ := PrimeFiltration.Restrict.proof S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q
  have hRD : RestrictData Q.toSubSystem hxy Q'.toSubSystem r :=
    ⟨fun I => (hr I).1, fun I => (hr I).2.1, fun I => (hr I).2.2.1, fun I => (hr I).2.2.2⟩
  obtain ⟨E1⟩ := hRQ S Ω N x pp hpp hhom hle j hj hj' K' ψ hker hxy Q Q' r hRD c 0

  obtain ⟨E2⟩ := hH0 S K' N _ K' (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)) hy0
  have hfin := (hFS S K' N _ (Q'.tensorProd (twistBundle S _ c)) hy0).1
  have hfin' : Module.Finite S (Q'.toSubSystem.twist (twistSys S (fun l => ψ (ratio hj l)) c)).secs := hfin
  exact Module.Finite.equiv (E1.trans E2).symm
end
end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Sections

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem mul_mem_pow_succ (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) : a * q ∈ (Q.pow (m + 1)).sub I :=
  Submodule.subset_span ⟨q, hq, a, ha, by rw [smul_eq_mul, mul_comm]⟩

theorem mul_pow_mem_pow (Q : SubSystem k x Ω) (I : Chart x) {m : ℕ} {a q : Ω}
    (ha : a ∈ (Q.pow m).sub I) (hq : q ∈ Q.sub I) (j : ℕ) : a * q ^ j ∈ (Q.pow (m + j)).sub I := by
  induction j with
  | zero => simpa using ha
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, ← add_assoc]
    exact mul_mem_pow_succ Q I ih hq

theorem aeval_mem_pow (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (I : Chart x) {f : MvPolynomial (Fin (r + 1)) k} {n : ℕ} (hf : f.IsHomogeneous n) :
    aeval h f ∈ (Q.pow n).sub I := by
  have hI : ∀ l, h l ∈ Q.sub I := fun l =>
    (Submodule.restrictScalars_mem k _ _).mp ((Submodule.mem_iInf _).mp (hh l) I)
  have hprod : ∀ (α : Fin (r + 1) →₀ ℕ) (s : Finset (Fin (r + 1))),
      ∏ i ∈ s, h i ^ α i ∈ (Q.pow (∑ i ∈ s, α i)).sub I := by
    intro α s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      exact one_mem_twistMod_zero (S := k) I
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, mul_comm, add_comm]
      exact mul_pow_mem_pow Q I ih (hI j) (α j)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [aeval_monomial]
  have hdeg : ∑ i ∈ α.support, α i = n := by
    have := hf (mem_support_iff.mp hα)
    rw [Finsupp.weight_apply, Finsupp.sum] at this
    simpa using this
  have hmem := hprod α α.support
  rw [hdeg] at hmem
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  exact Submodule.smul_of_tower_mem _ _ hmem

theorem coordGraded_le_secs (Q : SubSystem k x Ω) {r : ℕ} {h : Fin (r + 1) → Ω} (hh : ∀ l, h l ∈ Q.secs)
    (n : ℕ) : (coordGraded k h).piece (n : ℤ) ≤ (twistMul Q n 0).secs := by
  rw [twistMul, SubSystem.twist_twistSys_zero]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  have hen : e = n := by exact_mod_cast he
  subst hen
  exact (Submodule.mem_iInf _).mpr fun I =>
    (Submodule.restrictScalars_mem k _ _).mpr (aeval_mem_pow Q hh I hf)

theorem finite_secs_twistMul (hTF : TwistFinite.Statement.{u, w}) (Nb : LineBundle k x) {r : ℕ}
    {h : Fin (r + 1) → Ω} (hx : x ≠ 0) (hV : IsVeryAmpleBy Nb.toSubSystem h) (n : ℕ) :
    Module.Finite k (twistMul Nb.toSubSystem n 0).secs := by
  obtain ⟨m, deg, gen, -, hspan⟩ :=
    hTF k Ω N x (twistBundle k x 0) Nb r h hx hV.mem_secs hV.generates
  have e1 : (twistBundle k x 0).toSubSystem.twist (Nb.toSubSystem.pow n) =
      twistMul Nb.toSubSystem n 0 := by
    rw [twistMul, SubSystem.twist_twistSys_zero]
    exact twistSys_zero_twist _
  have hle := hspan n
  rw [e1] at hle
  let T : Submodule k Ω := ⨆ j : Fin m, (homogeneousSubmodule (Fin (r + 1)) k (n - deg j)).map
    ((LinearMap.mulRight k (gen j)).comp (aeval h).toLinearMap)
  have hT : T.FG := Submodule.fg_iSup _ fun j => (homogeneousSubmodule_fg (Fin (r + 1)) k (n - deg j)).map _
  have hle' : Submodule.span k {z | ∃ (j : Fin m) (f : MvPolynomial (Fin (r + 1)) k) (e : ℕ),
      f.IsHomogeneous e ∧ e + deg j = n ∧ z = aeval h f * gen j} ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, f, e, hf, hed, rfl⟩
    refine Submodule.mem_iSup_of_mem j ⟨f, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_homogeneousSubmodule]
    convert hf using 1
    omega
  have : FiniteDimensional k T := Module.Finite.iff_fg.mpr hT
  exact Submodule.finiteDimensional_of_le (hle.trans hle')

end Sections

theorem SectionCount.Top.proof (hHP : HilbertPositive.Statement.{u, w})
    (hTie : InterNumTie.Statement.{u, w}) (hTF : TwistFinite.Statement.{u, w})
    (hDim : VeryAmpleDim.Statement.{u, w}) (hDeg : VeryAmpleDegree.Statement.{u, w}) :
    SectionCount.Top.Statement.{u, w} := by
  intro k _ Ω _ _ N x d Nb hZ hN
  obtain ⟨r, h, hV⟩ := hN
  have hx : x ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := hZ.relevant
    exact hi ((mem_primeOf_of_isHomogeneous _ (isHomogeneous_X k i)).mpr (by simp))
  have hZh := hDim k Ω N x (d + 1) Nb r h hZ hV
  obtain ⟨⟨C, hC⟩, -, -⟩ := hHP k Ω r h (d + 1) (Nat.le_add_left 1 d) hZh
  have hnum : interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) =
      NumbersDVR.intNum k (primeOfOne (S := k) h) (fun _ : Fin (d + 1) => fun _ : Unit => (1 : ℤ)) := by
    rw [hDeg k Ω N x (d + 1) Nb r h hZ hV]
    exact hTie k Ω r h (d + 1) (primeOf (S := k) h) (fun _ => 1) hZh
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  have hle : (Module.finrank k ((coordGraded k h).piece (n : ℤ)) : ℝ) ≤
      (Module.finrank k (twistMul Nb.toSubSystem n 0).secs : ℝ) := by
    have := finite_secs_twistMul hTF Nb hx hV n
    exact_mod_cast Submodule.finrank_mono (coordGraded_le_secs Nb.toSubSystem hV.mem_secs n)
  rw [hnum]
  rw [Nat.add_sub_cancel] at hn
  have := (abs_le.mp hn).1
  linarith

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section JProper

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem twist_sub_eq_mul (F Q : SubSystem S x Ω) (I : Chart x) :
    (F.twist Q).sub I = Q.sub I * F.sub I := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    exact Submodule.mul_mem_mul hq hy
  · refine Submodule.mul_le.mpr fun q hq y hy => Submodule.subset_span ⟨q, hq, y, hy, rfl⟩

def ChartInvertible {I : Chart x} (P : Submodule (chartRing S x I) Ω) : Prop :=
  ∃ Q' : Submodule (chartRing S x I) Ω, P * Q' = 1

theorem ChartInvertible.mul {I : Chart x} {P P' : Submodule (chartRing S x I) Ω}
    (h : ChartInvertible P) (h' : ChartInvertible P') : ChartInvertible (P * P') := by
  obtain ⟨Q, hQ⟩ := h
  obtain ⟨Q', hQ'⟩ := h'
  exact ⟨Q * Q', by rw [mul_mul_mul_comm, hQ, hQ', one_mul]⟩

theorem chartInvertible_twistSys (c : ℤ) (I : Chart x) :
    ChartInvertible ((twistSys S x c).sub I) :=
  (twistBundle S x c).invertible I

theorem chartInvertible_twistMul (M : LineBundle S x) (p : ℕ) (m : ℤ) (I : Chart x) :
    ChartInvertible ((twistMul M.toSubSystem p m).sub I) := by
  have hpow : ∀ n : ℕ, ChartInvertible ((M.toSubSystem.pow n).sub I) := by
    intro n
    induction n with
    | zero => exact chartInvertible_twistSys 0 I
    | succ n ih =>
      change ChartInvertible (((M.toSubSystem.pow n).twist M.toSubSystem).sub I)
      rw [twist_sub_eq_mul]
      exact ChartInvertible.mul (M.invertible I) ih
  rw [twistMul, twist_sub_eq_mul]
  exact ChartInvertible.mul (chartInvertible_twistSys m I) (hpow p)

theorem aeval_mul_mem_twistMod {I : Chart x} {G : Poly S N} {b : ℕ} (hG : G.IsHomogeneous b) {a : ℤ}
    {o : Ω} (ho : o ∈ twistMod S x a I) : aeval x G * o ∈ twistMod S x (a + b) I := by
  refine Submodule.span_induction (p := fun o _ => aeval x G * o ∈ twistMod S x (a + b) I)
    ?_ ?_ ?_ ?_ ho
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    refine Submodule.subset_span ⟨G * f, s, e, b + e', hs, hG.mul hf, hse, by push_cast; omega, ?_⟩
    rw [map_mul, mul_div_assoc]
  · rw [mul_zero]; exact Submodule.zero_mem _
  · intro y z _ _ hy hz; rw [mul_add]; exact Submodule.add_mem _ hy hz
  · intro r z _ hz
    rw [chartRing_smul_def, mul_left_comm, ← chartRing_smul_def]
    exact Submodule.smul_mem _ r hz

theorem exists_form_chart {I : Chart x} {P : Submodule (chartRing S x I) Ω} (hP : ChartInvertible P)
    {σ : Ω} (hσ : σ ∈ P) (hσ0 : σ ≠ 0) : ∃ (g : Poly S N) (e : ℕ), g.IsHomogeneous e ∧
      aeval x g ≠ 0 ∧ ∀ δ ∈ P, ∃ o ∈ twistMod S x (e : ℤ) I, aeval x g * δ = σ * o := by
  obtain ⟨Q', hQ'⟩ := hP
  have hq : ∃ q ∈ Q', q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hbot : Q' = ⊥ := (Submodule.eq_bot_iff _).mpr hcon
    have h1 : (1 : Ω) ∈ (1 : Submodule (chartRing S x I) Ω) := Submodule.mem_one.mpr ⟨1, map_one _⟩
    rw [← hQ', hbot, Submodule.mul_bot, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  obtain ⟨q, hqQ, hq0⟩ := hq
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hσ hqQ :
    σ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨g, s, e, hs, hg, hse, hbg⟩ := b.2
  have hs0 := eval_ne_zero_of_mem_monos I hs
  have hb' : (b : Ω) = σ * q := hb
  have hgx : aeval x g = σ * q * aeval x s := by
    rw [← hb', hbg, div_mul_cancel₀ _ hs0]
  refine ⟨g, e, hg, by rw [hgx]; exact mul_ne_zero (mul_ne_zero hσ0 hq0) hs0, fun δ hδ => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hQ' ▸ Submodule.mul_mem_mul hδ hqQ :
    δ * q ∈ (1 : Submodule (chartRing S x I) Ω))
  obtain ⟨h, t, e', ht, hh, hte, hah⟩ := a.2
  have ha' : aeval x h / aeval x t = δ * q := by rw [← hah]; exact ha
  refine ⟨aeval x (s * h) / aeval x t,
    Submodule.subset_span ⟨s * h, t, e', e + e', ht, hse.mul hh, hte, by push_cast; ring, rfl⟩, ?_⟩
  rw [map_mul, mul_div_assoc, ha', hgx]
  ring

end JProper

theorem StepData.JProper.proof : StepData.JProper.Statement.{u, w} := by
  classical
  intro k _ Ω _ _ N x T
  have hloc : ∀ I : Chart x, ∃ (g : Poly k N) (e : ℕ), g.IsHomogeneous e ∧ aeval x g ≠ 0 ∧
      ∀ δ ∈ T.D.sub I, ∃ o ∈ twistMod k x (e : ℤ) I, aeval x g * δ = T.si * o := fun I =>
    exists_form_chart (chartInvertible_twistMul T.M T.p (T.m - T.c₁) I)
      ((Submodule.mem_iInf _).mp T.si_mem I) T.si_ne
  choose g e hg hg0 hgD using hloc
  refine ⟨∏ I, g I, ∑ I, e I, Ideal.subset_span ⟨∑ I, e I, IsHomogeneous.prod _ _ _
    fun I _ => hg I, fun I δ hδ => ?_⟩, IsHomogeneous.prod _ _ _ fun I _ => hg I, ?_⟩
  · obtain ⟨o, ho, hδo⟩ := hgD I δ hδ
    have hrest : (∏ J ∈ Finset.univ.erase I, g J).IsHomogeneous (∑ J ∈ Finset.univ.erase I, e J) :=
      IsHomogeneous.prod _ _ _ fun J _ => hg J
    refine ⟨aeval x (∏ J ∈ Finset.univ.erase I, g J) * o, ?_, ?_⟩
    · have hm := aeval_mul_mem_twistMod hrest ho
      have hdeg : ((e I : ℕ) : ℤ) + ((∑ J ∈ Finset.univ.erase I, e J : ℕ) : ℤ) =
          ((∑ J, e J : ℕ) : ℤ) := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ I)]; push_cast; ring
      rwa [hdeg] at hm
    · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ I), map_mul, mul_comm (aeval x (g I)),
        mul_assoc, hδo]
      ring
  · rw [mem_primeOf_of_isHomogeneous x (IsHomogeneous.prod _ _ _ fun I _ => hg I), map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun I _ => hg0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem FinGradedSub.tildeSys_natCast_eq_twist (M : FinGradedSub (S := S) (x := x) E) (a : ℕ) :
    M.tildeSys (a : ℤ) = (M.tildeSys 0).twist (twistSys S x (a : ℤ)) := by
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have hA : x i ^ a ∈ twistMod S x (a : ℤ) I := by
    rw [twistMod_eq_span _ I hi, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    refine Submodule.subset_span ⟨x i ^ a, hA, (aeval x (s * X i ^ a))⁻¹ • m,
      Submodule.subset_span ⟨m, s * X i ^ a, b, e + a, mul_mem hs (pow_mem (X_mem_monos hi) a),
        hse.mul (isHomogeneous_X_pow i a), hm, by push_cast; omega, rfl⟩, ?_⟩
    rw [smul_smul, map_mul, map_pow, aeval_X, mul_inv, ← mul_assoc, mul_comm (x i ^ a),
      mul_assoc, mul_inv_cancel₀ (pow_ne_zero a hxi), mul_one]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x (a : ℤ) I at hq
    rw [twistMod_eq_span _ I hi, zpow_natCast, Submodule.mem_span_singleton] at hq
    obtain ⟨β, rfl⟩ := hq
    have key : x i ^ a • y ∈ M.tilde (a : ℤ) I := by
      refine Submodule.span_induction (p := fun y _ => x i ^ a • y ∈ M.tilde (a : ℤ) I) ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨m, s, b, e, hs, hse, hm, hbe, rfl⟩
        refine Submodule.subset_span ⟨aeval x (X i ^ a : Poly S N) • m, s, b + a, e, hs, hse,
          M.smul_mem a b _ m (isHomogeneous_X_pow i a) hm, by omega, ?_⟩
        rw [smul_smul, smul_smul, map_pow, aeval_X, mul_comm]
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · intro y y' _ _ h h'
        rw [smul_add]
        exact Submodule.add_mem _ h h'
      · intro c y _ h
        rw [Subalgebra.smul_def, smul_smul, mul_comm, ← smul_smul, ← Subalgebra.smul_def]
        exact Submodule.smul_mem _ c h
    rw [SetLike.mem_coe, chartRing_smul_def, ← smul_smul, ← Subalgebra.smul_def]
    exact Submodule.smul_mem _ β key

end Tilde

theorem AmpleVanish.proof (hC : VeryAmpleCech.Statement.{u, v, w}) (hE : Extension.Statement.{u, v, w})
    (hT : TildeVanish.Statement.{u, v, w}) : AmpleVanish.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ F hF H hH
  obtain ⟨r, h, hh⟩ := hH
  obtain ⟨F', hF', hiso⟩ := hC S Ω N x E F hF H r h hh
  obtain ⟨M, -, hM⟩ := hE S Ω r h E F' hF'
  obtain ⟨c₀, hc₀⟩ := hT S Ω r h E M
  refine ⟨c₀.toNat, fun i a hi ha => ?_⟩
  obtain ⟨e⟩ := hiso a i
  have hsys : F'.toSubSystem = M.tildeSys 0 := SubSystem.ext_sub fun J => (hM J).symm
  have hv := hc₀ i hi a (by omega)
  rw [M.tildeSys_natCast_eq_twist a, ← hsys] at hv
  exact e.toEquiv.subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end
