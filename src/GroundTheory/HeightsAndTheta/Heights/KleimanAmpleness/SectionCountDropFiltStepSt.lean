module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltStepSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SectionCount.Drop.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Q : LineBundle S x) (J₁ pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ J₁, ∀ d : ℕ, homogeneousComponent d f ∈ J₁) → primeOf (S := S) x ≤ J₁ →
    g.IsHomogeneous e → (∀ f, f ∈ pp ↔ f * g ∈ J₁) →
    ∃ φ : (Q.twist (idealSys x (J₁ ⊔ Ideal.span {g}))).secs →ₗ[S]
        SubSystem.quotH (Q.twist (twistSys S x (-(e : ℤ))))
          ((Q.twist (twistSys S x (-(e : ℤ)))).twist (idealSys x pp)) 0,
      ∀ s, φ s = 0 → (s : Ω) ∈ (Q.twist (idealSys x J₁)).secs

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

theorem SerreVanish.equiv (hC : GradedCech.Statement) :
    Kleiman.SerreVanish.Statement.{0, 0} ↔ IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement := by
  constructor
  · intro hA S _ _ N M _ _ _ _ G hfin
    obtain ⟨c₀, hc₀⟩ := hA S N M (gradedEquiv S N M G) hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).injective.subsingleton
  · intro hB S _ _ N M _ _ _ _ 𝓜 hfin
    obtain ⟨G, rfl⟩ := (gradedEquiv S N M).surjective 𝓜
    obtain ⟨c₀, hc₀⟩ := hB S N M G hfin
    obtain ⟨e, -, -⟩ := hC S N
    refine ⟨c₀, fun i hi c hc => ?_⟩
    have := hc₀ i hi c hc
    exact (e M G i c).symm.injective.subsingleton

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem TwistVanish.proof (hE : Extension.Statement.{u, w, w}) (hV : SerreVanish.Statement.{u, w})
    (hT : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} := by
  intro S _ _ Ω _ _ N x G B r η hη hspan
  obtain ⟨M₀, -, hM₀⟩ := hE S Ω N x Ω G.toSubFamily G.fg
  obtain ⟨M, _, _, _, _, 𝓜, hfin, hsplit⟩ :=
    hT S Ω N x M₀ G.toSubSystem B.toSubSystem r η hM₀ hη hspan
  obtain ⟨c₀, hc₀⟩ := hV (MvPolynomial (Fin (r + 1)) S) N M 𝓜 hfin
  refine ⟨c₀, fun b c hc => ?_⟩
  obtain ⟨ι, π, hπ⟩ := hsplit b c 1
  have := hc₀ 1 le_rfl c hc
  exact ⟨fun z z' => by rw [← hπ z, ← hπ z', Subsingleton.elim (ι z) (ι z')]⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def SectionCount.Drop.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    IsVeryAmple Nb.toSubSystem → 1 ≤ b →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop, ∀ i < n,
      (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℝ) -
          (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℝ) ≤
        (interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem)) : ℝ) * (n : ℝ) ^ d / (d.factorial : ℝ) +
          C * (n : ℝ) ^ d / n

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropTermSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def SectionCount.Drop.Term.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (Nb : LineBundle k x) (b : ℕ) (pp : Ideal (Poly k N)) (e : ℕ) (c : ℤ),
    IsVeryAmple Nb.toSubSystem → IsSubvar x pp e →
    ∃ c' : ℕ, ∀ n i : ℕ,
      Module.Finite k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
        ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0) ∧
      Module.finrank k (SubSystem.quotH
          ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c))
          (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x c)).twist
            (idealSys x pp)) 0) ≤
        Module.finrank k (SubSystem.quotH (twistMul Nb.toSubSystem (n + c') 0)
          ((twistMul Nb.toSubSystem (n + c') 0).twist (idealSys x pp)) 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SectionCountDropFiltSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w


open Classical in
def SectionCount.Drop.Filt.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (Nb : LineBundle k x) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) → 1 ≤ b →
    ∃ β ∈ (twistSys k x (b : ℤ)).secs,
      (∃ I, β ∉ ((twistSys k x (b : ℤ)).twist (idealSys x (primeOf (S := k) x))).sub I) ∧
      ∃ (m : ℕ) (pp : Fin m → Ideal (Poly k N)) (e : Fin m → ℕ) (c : Fin m → ℤ),
        (∀ j, IsSubvar x (pp j) (e j) ∧ e j ≤ d ∧
          primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β ≤ pp j) ∧
        (∀ qq : Ideal (Poly k N),
          ((Finset.univ.filter fun j => e j = d ∧ pp j = qq).card : ℤ) =
            if h : qq ∈ (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β).minimalPrimes ∧
                IsSubvar x qq d then
              haveI : qq.IsPrime := h.1.1.1
              ((cutMult (primeOf (S := k) x ⊔ zeroIdeal (twistSys k x (b : ℤ)) β) qq).toNat : ℤ)
            else 0) ∧
        ∀ n i : ℕ,
          (Module.finrank k (twistMul Nb.toSubSystem n (-((i : ℤ) * b))).secs : ℤ) -
              (Module.finrank k (twistMul Nb.toSubSystem n (-(((i + 1 : ℕ) : ℤ) * b))).secs : ℤ) ≤
            ∑ j, (Module.finrank k (SubSystem.quotH
              ((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j)))
              (((twistMul Nb.toSubSystem n (-((i : ℤ) * b))).twist (twistSys k x (c j))).twist
                (idealSys x (pp j))) 0) : ℤ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

theorem VeryAmpleDegree.proof (hDim : VeryAmpleDim.Statement.{u, w})
    (hSecs : VeryAmpleSecs.Statement.{u, w}) (hHilb : VeryAmpleHilbert.Statement.{u, w}) :
    VeryAmpleDegree.Statement.{u, w} := by
  intro k _ Ω _ _ N x e Nb r h hZ hV
  obtain ⟨-, P, -, hP, hPn⟩ := hHilb k Ω N x e Nb hZ ⟨r, h, hV⟩
  obtain ⟨-, Q, -, hQ, hQn⟩ := hHilb k Ω r h e (twistBundle k h 1) (hDim k Ω N x e Nb r h hZ hV)
    isVeryAmple_twistSys_one
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hPn.and hQn)
  have hPQ : P = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => ((m + n₀ : ℕ) : ℚ)) ?_ ?_
    · intro a b hab
      have : a + n₀ = b + n₀ := by simpa using hab
      omega
    · intro m
      obtain ⟨h1, h2⟩ := hn₀ (m + n₀) (Nat.le_add_left n₀ m)
      change P.eval _ = Q.eval _
      rw [← h1, ← h2, hSecs k Ω N x Nb r h hV (m + n₀)]
      rfl
  have hnum : (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) =
      (interNum (primeOf (S := k) h) (fun _ : Fin e => twistSys k h 1) : ℚ) := by
    rw [← hP, hPQ, hQ]
    rfl
  exact_mod_cast hnum

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGlobalFunctionsIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

theorem GlobalFunctionsIntegral.proof : GlobalFunctionsIntegral.Statement := by
  intro k _ K _ _ N y a hy ha
  classical

  have key : ∀ i : Fin (N + 1), ∃ (e : ℕ) (f : MvPolynomial (Fin (N + 1)) k),
      f.IsHomogeneous e ∧ a * y i ^ e = aeval y f := by
    intro i
    by_cases hi : y i = 0
    · exact ⟨1, 0, isHomogeneous_zero _ _ _, by simp [hi]⟩
    · obtain ⟨f, s, e, hs, hf, hse, hrep⟩ := ha i hi
      obtain ⟨n, rfl⟩ := exists_eq_X_pow_of_mem_monos_single hs
      have hne : (X i ^ n : MvPolynomial (Fin (N + 1)) k) ≠ 0 := pow_ne_zero _ (X_ne_zero i)
      have hn : n = e := (isHomogeneous_X_pow i n).inj_right hse hne
      subst hn
      refine ⟨n, f, hf, ?_⟩
      have hyn : y i ^ n ≠ 0 := pow_ne_zero _ hi
      rw [hrep, map_pow, aeval_X, div_mul_cancel₀ _ hyn]
  choose e f hf hrel using key
  set E := ∑ i, e i with hE
  let M : Submodule k K :=
    (homogeneousSubmodule (Fin (N + 1)) k E).map (aeval y : MvPolynomial (Fin (N + 1)) k →ₐ[k] K).toLinearMap
  refine isIntegral_of_smul_mem_submodule M ?_ ((homogeneousSubmodule_fg (Fin (N + 1)) k E).map _) a ?_
  ·
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    refine (Submodule.ne_bot_iff M).mpr ⟨y i ^ E, ⟨X i ^ E, ?_, by simp⟩, pow_ne_zero _ hi⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X_pow i E)
  ·
    rintro _ ⟨g, hg, rfl⟩
    have hgE : g.IsHomogeneous E := (mem_homogeneousSubmodule _ _).mp hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, AlgHom.toLinearMap_apply, g.as_sum, map_sum, Finset.mul_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have hmE : m.degree = E := by
      by_contra h
      exact mem_support_iff.mp hm (hgE.coeff_eq_zero h)
    have hsum : ∑ i, e i ≤ ∑ i, m i := by
      rw [← hE, ← hmE, Finsupp.degree_eq_sum]
    obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
    set m' := m - Finsupp.single i (e i) with hm'
    have hsplit : m' + Finsupp.single i (e i) = m :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hi)
    have hdeg : m'.degree + e i = E := by
      rw [← hmE, ← hsplit, map_add (f := _), Finsupp.degree_single]
    refine ⟨monomial m' (AddMonoidAlgebra.coeff g m) * f i, ?_, ?_⟩
    · refine (mem_homogeneousSubmodule _ _).mpr ?_
      rw [← hdeg]
      exact (isHomogeneous_monomial _ rfl).mul (hf i)
    · have hmono : (monomial m (AddMonoidAlgebra.coeff g m) : MvPolynomial (Fin (N + 1)) k) =
          monomial m' (AddMonoidAlgebra.coeff g m) * X i ^ e i := by
        rw [X_pow_eq_monomial, monomial_mul, mul_one, hsplit]
      rw [AlgHom.toLinearMap_apply, map_mul, ← hrel i, hmono, map_mul, map_pow, aeval_X]
      ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

universe u w

theorem exists_pos_of_eventually_lower {d : ℕ} {A : ℤ} (hA : 0 < A) {C : ℝ} {f : ℕ → ℝ}
    (h : ∀ᶠ n : ℕ in atTop,
      (A : ℝ) * (n : ℝ) ^ (d + 1) / ((d + 1).factorial : ℝ) - C * (n : ℝ) ^ d ≤ f n)
    (D : ℕ) (hD : 0 < D) : ∃ n₁ : ℕ, 0 < n₁ ∧ 0 < f (D * n₁) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  obtain ⟨K, hK⟩ := exists_nat_gt (C * ((d + 1).factorial : ℝ) / A)
  refine ⟨n₀ + K + 1, by omega, ?_⟩
  have hle : n₀ + K + 1 ≤ D * (n₀ + K + 1) := Nat.le_mul_of_pos_left _ hD
  refine lt_of_lt_of_le ?_ (hn₀ _ (le_trans (by omega) hle))
  have hnK : (K : ℝ) < ((D * (n₀ + K + 1) : ℕ) : ℝ) := by
    have : K < D * (n₀ + K + 1) := lt_of_lt_of_le (by omega) hle
    exact_mod_cast this
  generalize ((D * (n₀ + K + 1) : ℕ) : ℝ) = n at hnK ⊢
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  have hF : (0 : ℝ) < ((d + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (Nat.cast_nonneg K) hnK
  have h1 : C * ((d + 1).factorial : ℝ) < A * n := by
    have := lt_trans hK hnK
    rwa [div_lt_iff₀ hA', mul_comm n] at this
  have h2 : C < A * n / ((d + 1).factorial : ℝ) := by rw [lt_div_iff₀ hF]; exact h1
  have h3 : (A : ℝ) * n ^ (d + 1) / ((d + 1).factorial : ℝ) - C * n ^ d =
      n ^ d * (A * n / ((d + 1).factorial : ℝ) - C) := by ring
  rw [h3]
  exact mul_pos (pow_pos hnpos d) (by linarith)

theorem sectionExists_of_gap (hcount : SectionCount.Statement.{u, w})
    (hlead : LeadingCoeffPos.Statement.{u, w}) {k : Type u} [Field k] {Ω : Type w} [Field Ω]
    [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω} {d : ℕ} {M : LineBundle k x} {t s' : ℚ}
    (hZ : IsSubvar x (primeOf (S := k) x) (d + 1)) (hM : Nef M.toSubSystem) (hs' : 0 < s')
    {Q : ℕ} {mQ : ℤ} (hQ : 0 < Q) (hmQ : (mQ : ℚ) = Q * t)
    (hva : IsVeryAmple (twistMul M.toSubSystem Q mQ))
    (hgap : 1 < (Q : ℚ) * (t / (d + 1) - s')) :
    ∃ (p : ℕ) (m c₁ : ℤ), 1 ≤ p ∧ (m : ℚ) = p * (t - s') ∧ 1 ≤ c₁ ∧
      ∃ σ ∈ (twistMul M.toSubSystem p (m - c₁)).secs, σ ≠ 0 := by
  obtain ⟨Nb, hNb⟩ := exists_lineBundle_twistMul M Q mQ
  have hvaN : IsVeryAmple Nb.toSubSystem := hNb ▸ hva

  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = ⌊(Q : ℚ) * s'⌋₊ + 1 := ⟨_, rfl⟩
  have hQs'0 : 0 ≤ (Q : ℚ) * s' := by positivity
  have hb_gt : (Q : ℚ) * s' < b := by rw [hb]; push_cast; exact Nat.lt_floor_add_one _
  have hb_le : (b : ℚ) ≤ Q * s' + 1 := by rw [hb]; push_cast; linarith [Nat.floor_le hQs'0]
  have hd0 : (d : ℚ) + 1 ≠ 0 := by positivity
  have hd : (0 : ℚ) < d + 1 := by positivity
  have hbT : (b : ℚ) < Q * (t / (d + 1)) := by
    have := hgap
    rw [mul_sub] at this
    linarith
  have hbm : ((d + 1 : ℕ) : ℤ) * b < mQ := by
    have h1 : ((d : ℚ) + 1) * b < (d + 1) * (Q * (t / (d + 1))) := mul_lt_mul_of_pos_left hbT hd
    have h2 : ((d : ℚ) + 1) * (Q * (t / (d + 1))) = Q * t := by field_simp
    have h3 : ((((d + 1 : ℕ) : ℤ) * b : ℤ) : ℚ) < (mQ : ℚ) := by
      push_cast
      rw [hmQ]
      linarith
    exact_mod_cast h3
  have hb1 : 1 ≤ b := by omega
  obtain ⟨C, hC⟩ := hcount k Ω N x d Nb b hZ hvaN hb1
  have hcoef := hlead k Ω N x d M Nb Q mQ b hZ hM hNb hvaN hbm

  have hden := Rat.mul_den_eq_num ((Q : ℚ) * s')
  have hD1 : 0 < ((Q : ℚ) * s').den := Rat.den_pos _
  generalize ((Q : ℚ) * s').den = D at hden hD1
  generalize ((Q : ℚ) * s').num = E at hden
  obtain ⟨n₁, hn₁, hpos⟩ := exists_pos_of_eventually_lower hcoef hC D hD1
  have hne : (twistMul Nb.toSubSystem (D * n₁) (-(((D * n₁ : ℕ) : ℤ) * b))).secs ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hpos
    simp at hpos
  obtain ⟨σ, hσ, hσne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [hNb, twistMul_twistMul] at hσ
  refine ⟨D * n₁ * Q, ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E, ((D * n₁ : ℕ) : ℤ) * b - n₁ * E,
    Nat.mul_pos (Nat.mul_pos hD1 hn₁) hQ, ?_, ?_, σ, ?_, hσne⟩
  · push_cast
    rw [hmQ, ← hden]
    ring
  · have hDn : (0 : ℚ) < (D : ℚ) * n₁ := by positivity
    have hpos' : (0 : ℚ) < ((((D * n₁ : ℕ) : ℤ) * b - n₁ * E : ℤ) : ℚ) := by
      push_cast
      rw [← hden]
      have key : (D : ℚ) * n₁ * (b - Q * s') = D * n₁ * b - n₁ * (Q * s' * D) := by ring
      have := mul_pos hDn (sub_pos.mpr hb_gt)
      linarith
    have : (0 : ℤ) < ((D * n₁ : ℕ) : ℤ) * b - n₁ * E := by exact_mod_cast hpos'
    omega
  · have hm : ((D * n₁ : ℕ) : ℤ) * mQ - n₁ * E - (((D * n₁ : ℕ) : ℤ) * b - n₁ * E) =
        ((D * n₁ : ℕ) : ℤ) * mQ + -(((D * n₁ : ℕ) : ℤ) * b) := by ring
    rw [hm]
    exact hσ

theorem SectionExists.proof (hcount : SectionCount.Statement.{u, w})
    (hpow : VeryAmplePow.Statement.{u, w}) (hlead : LeadingCoeffPos.Statement.{u, w}) :
    SectionExists.Statement.{u, w} := by
  intro k _ Ω _ _ N x d M t s' hZ hM hs' hst hq
  obtain ⟨q, m, hq1, hm, hva⟩ := hq
  have hδ : 0 < t / (d + 1) - s' := by linarith
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hq1
  have hqδ := mul_pos hqpos hδ
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt (1 / ((q : ℚ) * (t / (d + 1) - s')))
  rw [div_lt_iff₀ hqδ] at hj₀
  have hgap : 1 < (((j₀ + 1) * q : ℕ) : ℚ) * (t / (d + 1) - s') := by
    push_cast
    have : ((j₀ : ℚ) + 1) * q * (t / (d + 1) - s') =
        j₀ * (q * (t / (d + 1) - s')) + q * (t / (d + 1) - s') := by ring
    rw [this]
    linarith
  obtain ⟨Nb0, hNb0⟩ := exists_lineBundle_twistMul M q m
  have hvaQ : IsVeryAmple (twistMul M.toSubSystem ((j₀ + 1) * q) (((j₀ + 1 : ℕ) : ℤ) * m)) := by
    have := hpow k Ω N x Nb0 (j₀ + 1) (by rw [hNb0]; exact hva) (by omega)
    rw [hNb0, pow_twistMul] at this
    exact this
  exact sectionExists_of_gap hcount hlead hZ hM hs' (Nat.mul_pos (Nat.succ_pos _) hq1)
    (by push_cast; rw [hm]; ring) hvaQ hgap

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanishCech
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by
  unfold H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    sgn J j * sgn (J.erase j) k = -(sgn J k * sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cochain G 0) : d G ρ 1 (d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [d_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : face (face J ⟨j, hj⟩) ⟨k, hk⟩ =
        face (face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((face_subset _ _).trans (face_subset _ _))) hidx, ← add_smul]
    have hs : sgn J.1.1 j * sgn (face J ⟨j, hj⟩).1.1 k =
        -(sgn J.1.1 k * sgn (face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

end Cech

namespace SubSystem

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

section General

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem d_one_d_zero (F : SubSystem S x E) (w : Cech.Cochain (fun I => F.sub I) 0) :
    Cech.d (fun I => F.sub I) F.res 1 (Cech.d (fun I => F.sub I) F.res 0 w) = 0 :=
  Cech.d_one_d_zero (fun _ _ _ _ _ _ => rfl) w


set_option maxHeartbeats 1000000 in
theorem subsingleton_H_one_of_quot (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by
  unfold SubSystem.H at hG ⊢
  unfold quotH at hQ
  rw [Cech.subsingleton_H_one_iff] at hG hQ ⊢
  intro z hz
  let q : ∀ I, F.sub I →ₗ[S] (F.sub I ⧸ quotSub F G I) := fun I => (quotSub F G I).mkQ
  have hq : ∀ I J h m, q J (F.res I J h m) = quotRes F G I J h (q I m) := fun _ _ _ _ => rfl
  have hqd := Cech.mapC_d (R := S) (G := fun I => ↥(F.sub I))
    (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q hq
  obtain ⟨wb, hwb⟩ := hQ (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 z) (by rw [← hqd, hz, map_zero])
  choose w hw using fun I : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (wb I)
  have hmw : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 0 w) = wb := funext hw
  have hr : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 (z - Cech.d (fun I => F.sub I) F.res 0 w)) = 0 := by
    rw [map_sub, hqd 0, hmw, hwb]
    exact @sub_eq_zero_of_eq (Cech.Cochain (fun I => ↥(F.sub I) ⧸ quotSub F G I) 1) _ _ _ rfl
  have hrG : ∀ J, (((z - Cech.d (fun I => F.sub I) F.res 0 w) J : F.sub J.1) : E) ∈ G.sub J.1 :=
    fun J => (Submodule.Quotient.mk_eq_zero (quotSub F G J.1)).mp (congrFun hr J)
  let ι : ∀ I, G.sub I →ₗ[S] F.sub I := fun I =>
    { toFun := fun y => ⟨y, hGF I y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : ∀ I J h m, ι J (G.res I J h m) = F.res I J h (ι I m) := fun _ _ _ _ => rfl
  have hιd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι hι
  have hιinj : ∀ i, Function.Injective (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι i) := fun i a b hab =>
    funext fun I => Subtype.ext (congrArg (fun c => ((c I : F.sub I.1) : E)) hab)
  obtain ⟨g, hg⟩ : ∃ g : Cech.Cochain (fun I => ↥(G.sub I)) 1,
      (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 1 g) =
        z - Cech.d (fun I => F.sub I) F.res 0 w := ⟨fun J => ⟨_, hrG J⟩, rfl⟩
  have hdg : Cech.d (fun I => ↥(G.sub I)) G.res 1 g = 0 := by
    have h2 : (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι (1 + 1)
        (Cech.d (fun I => ↥(G.sub I)) G.res 1 g)) = 0 := by
      rw [hιd 1 g, hg, map_sub, hz, d_one_d_zero, sub_zero]
    exact hιinj (1 + 1) (h2.trans (LinearMap.map_zero _).symm)
  obtain ⟨v, hv⟩ := hG g hdg
  refine ⟨w + (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 0 v), ?_⟩
  rw [map_add (f := _), ← hιd, hv, hg, add_sub_cancel]

end General

theorem subsingleton_H_one_of_smul (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by
  unfold SubSystem.H at hF ⊢
  rw [Cech.subsingleton_H_one_iff] at hF ⊢
  have hdiv : ∀ I (z : G.sub I), σ⁻¹ * (z : Ω) ∈ F'.sub I := fun I z => by
    obtain ⟨y, hy, hzy⟩ := (hG I z).mp z.2
    rw [hzy, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    exact hy
  let φ : ∀ I, G.sub I →ₗ[S] F'.sub I := fun I =>
    { toFun := fun z => ⟨σ⁻¹ * z, hdiv I z⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ⁻¹ * (s • (a : Ω)) = s • (σ⁻¹ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  let ψ : ∀ I, F'.sub I →ₗ[S] G.sub I := fun I =>
    { toFun := fun y => ⟨σ * y, (hG I _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ * (s • (a : Ω)) = s • (σ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  have hφ : ∀ I J h m, φ J (G.res I J h m) = F'.res I J h (φ I m) := fun _ _ _ _ => rfl
  have hψ : ∀ I J h m, ψ J (F'.res I J h m) = G.res I J h (ψ I m) := fun _ _ _ _ => rfl
  have hφd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ hφ
  have hψd := Cech.mapC_d (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ hψ
  intro z hz
  obtain ⟨w, hw⟩ := hF (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ 1 z) (by rw [← hφd, hz, map_zero])
  refine ⟨(Cech.mapC (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ 0 w), ?_⟩
  rw [← hψd, hw]
  funext J
  apply Subtype.ext
  show σ * (σ⁻¹ * ((z J : G.sub J.1) : Ω)) = ((z J : G.sub J.1) : Ω)
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]

end SubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ResidOfMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

noncomputable section

section RestrictGenAux

variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω] {K' : Type} [Field K'] [Algebra F K']
  (R : Subalgebra F Ω) (σ : R →ₐ[F] K')


open Classical in
def RestrictGen.resid (a : Ω) : K' := if h : a ∈ R then σ ⟨a, h⟩ else 0

theorem RestrictGen.resid_of_mem {a : Ω} (h : a ∈ R) : RestrictGen.resid R σ a = σ ⟨a, h⟩ := dif_pos h

theorem RestrictGen.resid_zero : RestrictGen.resid R σ 0 = 0 := by
  rw [RestrictGen.resid_of_mem R σ (zero_mem R)]
  exact map_zero σ

theorem RestrictGen.resid_add {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a + b) = RestrictGen.resid R σ a + RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (add_mem ha hb), ← map_add]
  rfl

theorem RestrictGen.resid_mul {a b : Ω} (ha : a ∈ R) (hb : b ∈ R) :
    RestrictGen.resid R σ (a * b) = RestrictGen.resid R σ a * RestrictGen.resid R σ b := by
  rw [RestrictGen.resid_of_mem R σ ha, RestrictGen.resid_of_mem R σ hb,
    RestrictGen.resid_of_mem R σ (mul_mem ha hb), ← map_mul]
  rfl

end RestrictGenAux


open RestrictGen in
theorem RestrictGen.proof : RestrictGen.Statement := by
  intro F _ N Ω _ _ x K' _ _ x' hxy R σ hσ Q Q' c H ρ w w' hw' hQ hQ' hH
  classical
  have hσ' : ∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      aeval x f / aeval x g ∈ R ∧ resid R σ (aeval x f / aeval x g) = aeval x' f / aeval x' g := by
    intro f g m hf hg hg'
    obtain ⟨h, e⟩ := hσ f g m hf hg hg'
    exact ⟨h, by rw [resid_of_mem R σ h, e]⟩
  by_cases hx' : ∃ j, x' j ≠ 0
  swap
  · simp only [not_exists, not_not] at hx'
    have hI : IsEmpty (Kleiman.Chart x') := ⟨fun I => by
      obtain ⟨i, hi⟩ := I.2.1
      exact (Kleiman.mem_support x').mp (I.2.2 hi) (hx' i)⟩
    exact ⟨0, ⟨fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I, fun I => hI.elim I⟩⟩
  obtain ⟨j, hj⟩ := hx'
  have hxj : x j ≠ 0 := hxy j hj
  set r : Ω → K' := fun q => resid R σ (q * x j ^ c * w) / (x' j ^ c * w') with hr

  have hrat : ∀ i, x' i ≠ 0 → (x j / x i) ^ c ∈ R ∧ resid R σ ((x j / x i) ^ c) = (x' j / x' i) ^ c := by
    intro i hi
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · have := hσ' (X j ^ n) (X i ^ n) n (isHomogeneous_X_pow (R := F) j n) (isHomogeneous_X_pow (R := F) i n)
        (by simpa using pow_ne_zero n hi)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_natCast, div_pow] using this
    · have := hσ' (X i ^ n) (X j ^ n) n (isHomogeneous_X_pow (R := F) i n) (isHomogeneous_X_pow (R := F) j n)
        (by simpa using pow_ne_zero n hj)
      simp only [map_pow, aeval_X] at this
      simpa [zpow_neg, zpow_natCast, div_pow, inv_div] using this

  have hchart : ∀ (I : Kleiman.Chart x') (a : Ω), a ∈ Kleiman.chartRing F x (Kleiman.liftChart hxy I) →
      a ∈ R ∧ resid R σ a ∈ Kleiman.chartRing F x' I := by
    rintro I a ⟨f, s, e, hs, hf, hse, rfl⟩
    obtain ⟨h1, h2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    exact ⟨h1, h2 ▸ ⟨f, s, e, hs, hf, hse, rfl⟩⟩

  have hspan : ∀ (I : Kleiman.Chart x') (z : Ω),
      z ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H →
      z * w ∈ R ∧ resid R σ (z * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I z hz
    induction hz using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨hm, e⟩ := hH h hh
      refine ⟨hm, ?_⟩
      rw [resid_of_mem R σ hm, e, mul_div_cancel_right₀ _ hw']
      exact Submodule.subset_span ⟨h, hh, rfl⟩
    | zero =>
      rw [zero_mul, resid_zero, zero_div]
      exact ⟨zero_mem R, zero_mem _⟩
    | add a b _ _ ha hb =>
      refine ⟨by rw [add_mul]; exact add_mem ha.1 hb.1, ?_⟩
      rw [add_mul, resid_add R σ ha.1 hb.1, add_div]
      exact add_mem ha.2 hb.2
    | smul a z _ hz =>
      obtain ⟨ha1, ha2⟩ := hchart I a a.2
      rw [Kleiman.chartRing_smul_def, mul_assoc]
      refine ⟨mul_mem ha1 hz.1, ?_⟩
      rw [resid_mul R σ ha1 hz.1, mul_div_assoc]
      exact Submodule.smul_mem _ (⟨_, ha2⟩ : Kleiman.chartRing F x' I) hz.2

  have hkey : ∀ (I : Kleiman.Chart x') (i : Fin (N + 1)), i ∈ I.1 → ∀ q ∈ Q.sub (Kleiman.liftChart hxy I),
      q * x j ^ c * w ∈ R ∧ r q * x' i ^ c = resid R σ (x i ^ c * q * w) / w' ∧
      resid R σ (x i ^ c * q * w) / w' ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
    intro I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    have hxi : x i ≠ 0 := hxy i hx'i
    have hz : x i ^ c * q ∈ Submodule.span (Kleiman.chartRing F x (Kleiman.liftChart hxy I)) H := by
      rw [← hQ (Kleiman.liftChart hxy I)]
      exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mpr ⟨q, hq, rfl⟩
    obtain ⟨hz1, hz2⟩ := hspan I _ hz
    obtain ⟨hr1, hr2⟩ := hrat i hx'i
    have heq : q * x j ^ c * w = (x j / x i) ^ c * (x i ^ c * q * w) := by
      rw [div_zpow]
      field_simp
    refine ⟨heq ▸ mul_mem hr1 hz1, ?_, hz2⟩
    rw [hr]
    dsimp only
    rw [heq, resid_mul R σ hr1 hz1, hr2, div_zpow]
    field_simp
  have hmem : ∀ (I : Kleiman.Chart x'), ∀ q ∈ Q.sub (Kleiman.liftChart hxy I), r q ∈ Q'.sub I := by
    intro I q hq
    obtain ⟨i, hi⟩ := I.2.1
    obtain ⟨-, e, hm⟩ := hkey I i hi q hq
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    rw [← hQ' I] at hm
    obtain ⟨y, hy, hy'⟩ := (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mp hm
    have h' : r q * x' i ^ c = y * x' i ^ c := by
      rw [e, hy', smul_eq_mul, mul_comm]
    rw [mul_right_cancel₀ (zpow_ne_zero c hx'i) h']
    exact hy
  refine ⟨r, ⟨hmem, ?_, ?_, ?_⟩⟩
  · intro I q hq q' hq'
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    have h2 := (hkey I i hi q' hq').1
    rw [hr]
    dsimp only
    rw [add_mul, add_mul, resid_add R σ h1 h2, add_div]
  · intro I q hq f s e hs hf hse
    obtain ⟨i, hi⟩ := I.2.1
    have h1 := (hkey I i hi q hq).1
    obtain ⟨ha1, ha2⟩ := hσ' f s e hf hse (Kleiman.eval_ne_zero_of_mem_monos I hs)
    have hm : aeval x f / aeval x s * q * x j ^ c * w = aeval x f / aeval x s * (q * x j ^ c * w) := by ring
    rw [hr]
    dsimp only
    rw [hm, resid_mul R σ ha1 h1, ha2, mul_div_assoc]
  · intro I
    obtain ⟨i, hi⟩ := I.2.1
    have hx'i : x' i ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi)
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨q, hq, rfl⟩
      exact hmem I q hq
    · intro t ht
      have ht' : x' i ^ c * t ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H) := by
        rw [← hQ' I]
        exact (TranslateEq.mem_twist_twistSys_iff Q'.toSubSystem c I hi _).mpr ⟨t, ht, rfl⟩
      have hall : ∀ u ∈ Submodule.span (Kleiman.chartRing F x' I) (ρ '' H),
          x' i ^ (-c) * u ∈ Submodule.span (Kleiman.chartRing F x' I) (r '' Q.sub (Kleiman.liftChart hxy I)) := by
        intro u hu
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨h, hh, rfl⟩ := hu
          have hh' : h ∈ (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub (Kleiman.liftChart hxy I) := by
            rw [hQ]
            exact Submodule.subset_span hh
          obtain ⟨y, hy, rfl⟩ :=
            (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem c (Kleiman.liftChart hxy I) hi _).mp hh'
          obtain ⟨hm, e⟩ := hH _ hh
          obtain ⟨-, e', -⟩ := hkey I i hi y hy
          have e'' : resid R σ (x i ^ c * y * w) = ρ (x i ^ c • y) * w' := (resid_of_mem R σ hm).trans e
          rw [e'', mul_div_cancel_right₀ _ hw'] at e'
          have : x' i ^ (-c) * ρ (x i ^ c • y) = r y := by
            rw [← e', zpow_neg]
            field_simp
          rw [this]
          exact Submodule.subset_span ⟨y, hy, rfl⟩
        | zero => rw [mul_zero]; exact zero_mem _
        | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
        | smul a u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_left_comm]
          exact Submodule.smul_mem _ a hu
      have := hall _ ht'
      rwa [← mul_assoc, ← zpow_add₀ hx'i, neg_add_cancel, zpow_zero, one_mul] at this

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCutMultPos
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

open IsLocalRing

def locQuotEquiv {R : Type*} [CommRing R] (q : Ideal R) [q.IsPrime] (J : Ideal R) :
    (Localization.AtPrime q ⧸ J.localized' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q))) ≃ₗ[Localization.AtPrime q]
      LocalizedModule q.primeCompl (R ⧸ J) :=
  have := IsLocalization.linearMap_compatibleSMul q.primeCompl
  (IsLocalizedModule.linearEquiv q.primeCompl
    (J.toLocalizedQuotient' (Localization.AtPrime q) q.primeCompl
      (Algebra.linearMap R (Localization.AtPrime q)))
    (LocalizedModule.mkLinearMap _ _)).restrictScalars _

theorem CutMultPos.proof : CutMultPos.Statement := by
  intro S _ _ N J qq h
  have : qq.IsPrime := h.1.1
  let J' : Ideal (Localization.AtPrime qq) :=
    J.localized' (Localization.AtPrime qq) qq.primeCompl
      (Algebra.linearMap (Poly S N) (Localization.AtPrime qq))
  have hJ' : J' = J.map (algebraMap (Poly S N) (Localization.AtPrime qq)) := by
    simp only [J', Submodule.localized'_eq_span, Ideal.map]
    rfl
  have hmin : maximalIdeal (Localization.AtPrime qq) ∈ J'.minimalPrimes := by
    rw [hJ', IsLocalization.minimalPrimes_map qq.primeCompl, Set.mem_preimage,
      Localization.AtPrime.under_maximalIdeal]
    exact h
  have hne : J' ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hmin.1.2
  have : Nontrivial (Localization.AtPrime qq ⧸ J') := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsArtinianRing (Localization.AtPrime qq ⧸ J') :=
    quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J' hmin
  have : IsArtinian (Localization.AtPrime qq) (Localization.AtPrime qq ⧸ J') :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := J'))
  have : IsNoetherianRing (Localization.AtPrime qq) :=
    IsLocalization.isNoetherianRing qq.primeCompl _ inferInstance
  unfold cutMult
  rw [← (locQuotEquiv qq J).length_eq]
  exact ⟨Module.length_pos, Module.length_ne_top.lt_top⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end
