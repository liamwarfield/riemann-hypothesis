module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AlgebraMapMemChartRingLine
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsDegLocExact

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def SubFamilyTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : LineBundle S x), (∀ I, (F.sub I).FG) →
    ∃ G : SubFamily S x E, G.toSubSystem = F.toSubSystem.twist Q.toSubSystem ∧ ∀ I, (G.sub I).FG

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CutDimLowerSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def CutDimLower.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (n : ℕ) (pp : Ideal (Poly k N)) (L : LineBundle k x) (s : Ω) (qq : Ideal (Poly k N)),
    IsSubvar x pp (n + 1) → s ∈ L.secs → qq ∈ (pp ⊔ zeroIdeal L.toSubSystem s).minimalPrimes →
    (∃ j, (X j : Poly k N) ∉ qq) → ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Poly k N ⧸ qq)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsCycleSplitSmall
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Small.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (M : LineBundle S x) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ pp : Ideal (Poly S N), pp.IsPrime → (∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp) →
    primeOf (S := S) x ≤ pp → 𝔪.map (C : S →+* Poly S N) ≤ pp → ringKrullDim (Poly S N ⧸ pp) ≤ 1 →
    ∀ᶠ c : ℕ in atTop, interSum pp ![M.toSubSystem] c = 0

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u w

def LeadingCoeffPos.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (d : ℕ)
    (M Nb : LineBundle k x) (q : ℕ) (m : ℤ) (b : ℕ), IsSubvar x (primeOf (S := k) x) (d + 1) →
    Nef M.toSubSystem → Nb.toSubSystem = twistMul M.toSubSystem q m → IsVeryAmple Nb.toSubSystem →
    ((d + 1 : ℕ) : ℤ) * b < m →
    0 < interNum (primeOf (S := k) x) (fun _ : Fin (d + 1) => Nb.toSubSystem) -
          ((d + 1 : ℕ) : ℤ) * interNum (primeOf (S := k) x)
            (Fin.cons (α := fun _ => SubSystem k x Ω) (twistSys k x (b : ℤ))
              (fun _ : Fin d => Nb.toSubSystem))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def RestrictGen.Statement : Prop :=
  ∀ (F : Type) [Field F] (N : ℕ) (Ω : Type) [Field Ω] [Algebra F Ω] (x : Fin (N + 1) → Ω)
    (K' : Type) [Field K'] [Algebra F K'] (x' : Fin (N + 1) → K') (hxy : ∀ i, x' i ≠ 0 → x i ≠ 0)
    (R : Subalgebra F Ω) (σ : R →ₐ[F] K'),
    (∀ (f g : Kleiman.Poly F N) (m : ℕ), f.IsHomogeneous m → g.IsHomogeneous m → aeval x' g ≠ 0 →
      ∃ h : aeval x f / aeval x g ∈ R, σ ⟨_, h⟩ = aeval x' f / aeval x' g) →
    ∀ (Q : Kleiman.LineBundle F x) (Q' : Kleiman.LineBundle F x') (c : ℤ) (H : Set Ω) (ρ : Ω → K') (w : Ω)
      (w' : K'), w' ≠ 0 →
      (∀ I, (Q.toSubSystem.twist (Kleiman.twistSys F x c)).sub I = Submodule.span (Kleiman.chartRing F x I) H) →
      (∀ I, (Q'.toSubSystem.twist (Kleiman.twistSys F x' c)).sub I =
        Submodule.span (Kleiman.chartRing F x' I) (ρ '' H)) →
      (∀ h ∈ H, ∃ hh : h * w ∈ R, σ ⟨_, hh⟩ = ρ h * w') →
      ∃ r : Ω → K', Kleiman.RestrictData Q.toSubSystem hxy Q'.toSubSystem r

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleHilbertSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def VeryAmpleHilbert.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ n : ℕ, FiniteDimensional k (Nb.toSubSystem.pow n).secs) ∧
    ∃ P : Polynomial ℚ, P.natDegree ≤ e ∧
      P.coeff e * (e.factorial : ℚ) =
        (interNum (primeOf (S := k) x) (fun _ : Fin e => Nb.toSubSystem) : ℚ) ∧
      ∀ᶠ n : ℕ in atTop, (Module.finrank k (Nb.toSubSystem.pow n).secs : ℚ) = P.eval (n : ℚ)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistTildeSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

def TwistTilde.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω),
    ∃ P : FinGradedSub (S := S) (x := x) E,
      (∀ c : ℤ, P.piece c = Submodule.span S {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧
        m ∈ M.piece b ∧ a + b = c ∧ z = q • m}) ∧
      ∀ I, ((M.tildeSys 0).twist (Q.tildeSys 0)).sub I = P.tilde 0 I

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleSnapperSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u w

def VeryAmpleSnapper.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ)
    (Nb : LineBundle k x), IsSubvar x (primeOf (S := k) x) e → IsVeryAmple Nb.toSubSystem →
    (∀ (a : ℕ) (c : ℤ), FiniteDimensional k (twistMul Nb.toSubSystem a c).secs) ∧
    ∃ (Q : MvPolynomial (Fin 2) ℚ) (c₀ : ℤ), Q.totalDegree ≤ e ∧
      (∀ (a : ℕ) (c : ℤ), c₀ ≤ c →
        (Module.finrank k (twistMul Nb.toSubSystem a c).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), (c : ℚ)] Q) ∧
      ∀ᶠ a : ℕ in atTop,
        (Module.finrank k (Nb.toSubSystem.pow a).secs : ℚ) = MvPolynomial.eval ![(a : ℚ), 0] Q

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CycleSplitFiltStepSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CycleSplit.Filt.Step.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (𝔪 : Ideal S), 𝔪.IsMaximal →
    ∀ (K pp : Ideal (Poly S N)) (g : Poly S N) (e : ℕ),
    (∀ f ∈ K, ∀ d : ℕ, homogeneousComponent d f ∈ K) → primeOf (S := S) x ≤ K →
    𝔪.map (C : S →+* Poly S N) ≤ K → g.IsHomogeneous e →
    (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) → (∀ f, f ∈ pp ↔ f * g ∈ K) →
    ∀ Q : LineBundle S x, ∀ᶠ c : ℕ in atTop,
      restrLen K (Q.twist (twistSys S x (c : ℤ))) =
        restrLen (K ⊔ Ideal.span {g}) (Q.twist (twistSys S x (c : ℤ))) +
          restrLen pp (Q.twist (twistSys S x ((c : ℤ) - e)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisAltBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq

open MvPolynomial

def GradedCech.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (N : ℕ),
    ∃ e : ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (i : ℕ) (c : ℤ),
        IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c ≃ₗ[S] Kleiman.cohom (gradedEquiv S N M G) i c,
      (∀ (M M' : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        [AddCommGroup M'] [Module (Poly S N) M'] [Module S M'] [IsScalarTower S (Poly S N) M']
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (G' : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M')
        (f : M →ₗ[Poly S N] M') (hf : IndefiniteRowSideFullHecke.Kleiman.IsGradedHom S N G G' f) (i : ℕ) (c : ℤ)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedH S N M G i c),
        e M' G' i c (IndefiniteRowSideFullHecke.Kleiman.gradedHmap S N hf i c z) =
          Kleiman.cohomMap (⟨f, fun c m hm => hf c m hm⟩ :
            Kleiman.GradedHom (gradedEquiv S N M G) (gradedEquiv S N M' G')) i c (e M G i c z)) ∧
      ∀ (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
        (G : IndefiniteRowSideFullHecke.Kleiman.GradedMod S N M) (c : ℤ) (m : M) (hm : m ∈ G.piece c)
        (z : IndefiniteRowSideFullHecke.Kleiman.gradedZ S N M G 0 c),
        (z : ∀ I, (IndefiniteRowSideFullHecke.Kleiman.gradedSys S N M G c).V I) = IndefiniteRowSideFullHecke.Kleiman.unitCochain S N M m →
        e M G 0 c (Submodule.Quotient.mk z) = Kleiman.toH0 (gradedEquiv S N M G) c ⟨m, hm⟩

end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechCone
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v

namespace Cech.Cone

section Signs

variable {n : ℕ}

theorem sgn_insert {a b : Fin n} {A : Finset (Fin n)} (ha : a ∉ A) :
    Cech.sgn (insert a A) b = Cech.sgn A b * (if a < b then -1 else 1) := by
  unfold Cech.sgn
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hm => ha (Finset.mem_filter.mp hm).1), pow_succ]
  · rw [mul_one]

theorem sgn_mul_self (A : Finset (Fin n)) (b : Fin n) : Cech.sgn A b * Cech.sgn A b = 1 := by
  unfold Cech.sgn
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem sgn_key {K : Finset (Fin n)} {i₀ j : Fin n} (hi₀ : i₀ ∉ K) (hj : j ∈ K) :
    Cech.sgn K j * Cech.sgn (insert i₀ (K.erase j)) i₀ =
      -(Cech.sgn (insert i₀ K) i₀ * Cech.sgn (insert i₀ K) j) := by
  have hne : j ≠ i₀ := fun e => hi₀ (e ▸ hj)
  have h1 : Cech.sgn (insert i₀ (K.erase j)) i₀ = Cech.sgn (K.erase j) i₀ := by
    rw [sgn_insert (fun hm => hi₀ (Finset.mem_of_mem_erase hm)), if_neg (lt_irrefl _), mul_one]
  have h2 : Cech.sgn (insert i₀ K) i₀ = Cech.sgn K i₀ := by
    rw [sgn_insert hi₀, if_neg (lt_irrefl _), mul_one]
  have h3 := sgn_insert (b := j) hi₀
  have h4 := sgn_insert (b := i₀) (Finset.notMem_erase j K)
  rw [Finset.insert_erase hj] at h4
  rw [h1, h2, h3, h4]
  rcases lt_or_gt_of_ne hne with h | h
  · simp only [if_pos h, if_neg (lt_asymm h)]; ring
  · simp only [if_neg (lt_asymm h), if_pos h]; ring

end Signs

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {N : ℕ}

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i) (A : Finset (Fin (N + 1))) : V :=
  if h : A.card = i + 1 then
    s ⟨⟨A, Finset.card_pos.mp (by omega), Finset.subset_univ A⟩, h⟩
  else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (I : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) : onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left I.2]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : StdCell N => V) i)
    (K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) (i + 1)) :
    Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

def coneY {i : ℕ} (i₀ : Fin (N + 1)) (z : Cech.Cochain (fun _ : StdCell N => V) (i + 1))
    (A : Finset (Fin (N + 1))) : V :=
  if i₀ ∈ A then 0 else Cech.sgn (insert i₀ A) i₀ • onSet z (insert i₀ A)

theorem onSet_pair {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    {a b : Fin (N + 1)} (hab : a < b) : onSet z {a} = onSet z {b} := by
  have hcard : ({a, b} : Finset (Fin (N + 1))).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hz ⟨⟨{a, b}, Finset.insert_nonempty _ _, Finset.subset_univ _⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin (N + 1))), Cech.sgn {a, b} j • onSet z (({a, b} : Finset _).erase j)
    = 0 at h
  have ha : a ∉ ({b} : Finset (Fin (N + 1))) := Finset.notMem_singleton.mpr hab.ne
  rw [Finset.sum_pair hab.ne, Finset.erase_insert ha, Finset.erase_insert_of_ne hab.ne,
    Finset.erase_singleton, sgn_insert ha, sgn_insert ha, if_neg (lt_irrefl _), if_pos hab] at h
  have e1 : Cech.sgn ({b} : Finset (Fin (N + 1))) a = 1 := by
    simp [Cech.sgn, Finset.filter_singleton, lt_asymm hab]
  have e2 : Cech.sgn ({b} : Finset (Fin (N + 1))) b = 1 := by
    simp [Cech.sgn, Finset.filter_singleton]
  rw [e1, e2, insert_empty_eq] at h
  rw [one_mul, one_smul, one_mul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const {z : Cech.Cochain (fun _ : StdCell N => V) 0}
    (hz : Cech.d (fun _ : StdCell N => V) (Cech.idRes R V Finset.univ) 0 z = 0)
    (I K : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0) : z I = z K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  rw [← onSet_idx z I, ← onSet_idx z K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hz h
  · rfl
  · exact (onSet_pair hz h).symm

end Cech.Cone


open Cech.Cone in
theorem Cech.Cone.proof : Cech.Cone.Statement.{u, v} := by
  intro R _ V _ _ N J
  refine ⟨?_, ?_, fun z hz I K => const hz I K⟩
  · intro W i₀ hi₀ i z hz hW hJ
    have hWs : ∀ A, onSet z A ∈ W := by
      intro A; unfold onSet; split_ifs
      · exact hW _
      · exact W.zero_mem
    have hJs : ∀ A, ¬ J ⊆ A → onSet z A = 0 := by
      intro A hA; unfold onSet; split_ifs
      · exact hJ _ hA
      · rfl
    have hcoc : ∀ L : Finset (Fin (N + 1)), L.card = i + 1 + 1 + 1 →
        ∑ j ∈ L, Cech.sgn L j • onSet z (L.erase j) = 0 := by
      intro L hL
      have h := congrFun hz ⟨⟨L, Finset.card_pos.mp (by omega), Finset.subset_univ L⟩, hL⟩
      rw [d_eq] at h
      exact h
    refine ⟨fun I => coneY i₀ z I.1.1, fun I => ?_, fun I hI => ?_, ?_⟩
    · change coneY i₀ z I.1.1 ∈ W
      unfold coneY; split_ifs
      · exact W.zero_mem
      · exact zsmul_mem (hWs _) _
    · change coneY i₀ z I.1.1 = 0
      unfold coneY; split_ifs
      · rfl
      · rw [hJs _ fun hs => hI fun x hx =>
          (Finset.mem_insert.mp (hs hx)).resolve_left fun (e : x = i₀) => hi₀ (e ▸ hx), smul_zero]
    · funext K
      rw [d_eq, ← onSet_idx z K]
      have hK : K.1.1.card = i + 1 + 1 := K.2
      have hY : ∀ j ∈ K.1.1, onSet (fun I => coneY i₀ z I.1.1 :
          Cech.Cochain (fun _ : StdCell N => V) i) (K.1.1.erase j) = coneY i₀ z (K.1.1.erase j) := by
        intro j hj
        unfold onSet
        rw [dite_eq_left (by rw [Finset.card_erase_of_mem hj, hK]; rfl)]
      rw [Finset.sum_congr rfl fun j hj => by rw [hY j hj]]
      generalize K.1.1 = Kf at hK ⊢
      by_cases h : i₀ ∈ Kf
      · rw [Finset.sum_eq_single i₀]
        · rw [coneY, if_neg (Finset.notMem_erase i₀ Kf), Finset.insert_erase h, smul_smul,
            sgn_mul_self, one_smul]
        · intro j hj hne
          rw [coneY, if_pos (Finset.mem_erase.mpr ⟨Ne.symm hne, h⟩), smul_zero]
        · exact fun h' => absurd h h'
      · have hc := hcoc (insert i₀ Kf) (by rw [Finset.card_insert_of_notMem h, hK])
        rw [Finset.sum_insert h, Finset.erase_insert h] at hc
        have hb := eq_neg_iff_add_eq_zero.mpr ((add_comm _ _).trans hc)
        have hs : ∑ j ∈ Kf, Cech.sgn Kf j • coneY i₀ z (Kf.erase j) =
            -(Cech.sgn (insert i₀ Kf) i₀ •
              ∑ j ∈ Kf, Cech.sgn (insert i₀ Kf) j • onSet z ((insert i₀ Kf).erase j)) := by
          rw [Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hne : i₀ ≠ j := fun e => h (e ▸ hj)
          have hni : i₀ ∉ Kf.erase j := fun hm => h (Finset.mem_of_mem_erase hm)
          rw [Finset.erase_insert_of_ne hne, coneY, if_neg hni, smul_smul, smul_smul,
            sgn_key h hj, neg_smul]
        rw [hs, hb, smul_neg, neg_neg, smul_smul, sgn_mul_self, one_smul]
  · intro hJne i₀ hi₀ z hz hJ
    obtain ⟨j, hj⟩ := hJne
    funext I
    let I₀ : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{i₀}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    rw [const hz I I₀]
    exact hJ I₀ fun hs => hi₀ (Finset.mem_singleton.mp (hs hj) ▸ hj)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCohomRetract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Retract

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem locMap_retract (f : M →ₗ[Poly S N] M') (g : M' →ₗ[Poly S N] M)
    (hgf : Function.LeftInverse g f) (I : Finset (Fin (N + 1))) :
    Function.LeftInverse (locMap g I) (locMap f I) := by
  intro x
  induction x using LocalizedModule.induction_on with
  | h m s => rw [locMap_mk, locMap_mk, hgf m]

theorem cohomMap_retract {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'}
    (f : GradedHom 𝓜 𝓜') (g : GradedHom 𝓜' 𝓜) (hgf : Function.LeftInverse g.toLin f.toLin)
    (i : ℕ) (c : ℤ) : Function.LeftInverse (cohomMap g i c) (cohomMap f i c) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact congrArg Submodule.Quotient.mk
    (Subtype.ext (funext fun I => locMap_retract f.toLin g.toLin hgf I.1.1 (z.1 I)))

theorem CohomRetract.proof : CohomRetract.Statement.{u, v, w} := by
  intro S _ N M M' _ _ _ _ _ _ _ _ 𝓜 𝓜' f g hgf i c
  exact (cohomMap_retract f g hgf i c).injective

end Retract

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedULift
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem GradedULift.proof : GradedULift.Statement.{u, v} := by
  intro S _ N M _ _ _ _ 𝓜
  let e : M ≃ₗ[S] ULift.{u} M := (ULift.moduleEquiv (R := S)).symm
  let eP : M ≃ₗ[Poly S N] ULift.{u} M := (ULift.moduleEquiv (R := Poly S N)).symm
  let pc : ℤ → Submodule S (ULift.{u} M) := fun c => (𝓜.piece c).map (e : M →ₗ[S] ULift.{u} M)
  have hpc : ∀ c, pc c = Submodule.orderIsoMapComap e (𝓜.piece c) := fun _ => rfl
  have hint : DirectSum.IsInternal pc := by
    have h0 := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).1 𝓜.isInternal
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).2 ⟨?_, ?_⟩
    · have : pc = (Submodule.orderIsoMapComap e) ∘ 𝓜.piece := funext hpc
      rw [this]
      exact h0.1.map_orderIso _
    · have h1 : (⨆ c, pc c) = Submodule.orderIsoMapComap e (⨆ c, 𝓜.piece c) := by
        rw [OrderIso.map_iSup]
        rfl
      rw [h1, h0.2]
      exact (Submodule.orderIsoMapComap e).map_top
  let 𝓜' : GradedPMod S N (ULift.{u} M) :=
    { piece := pc
      isInternal := hint
      smul_mem := by
        intro d c p m hp hm
        obtain ⟨x, hx, rfl⟩ := hm
        refine ⟨p • x, 𝓜.smul_mem d c p x hp hx, ?_⟩
        rfl }
  refine ⟨ULift.{u} M, inferInstance, inferInstance, inferInstance, inferInstance, 𝓜',
    ⟨eP.toLinearMap, fun c m hm => ⟨m, hm, rfl⟩⟩,
    ⟨eP.symm.toLinearMap, fun c m hm => ?_⟩, fun m => rfl, fun m => rfl⟩
  obtain ⟨x, hx, rfl⟩ := hm
  exact hx

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreFinite.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreFinite.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∀ i, N + 1 ≤ i + k → ∀ c : ℤ, Module.Finite S (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _ i hi c
      have := hTop S N M 𝓜 i c (by omega)
      exact ⟨by rw [Subsingleton.elim (⊤ : Submodule S (cohom 𝓜 i c)) ⊥]; exact Submodule.fg_bot⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM i hi c
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      have hF : Module.Finite S (cohom 𝓕 i c) := (hFree S N F 𝓕 r b d hb).1 i c
      have hKf : Module.Finite S (cohom 𝓚 (i + 1) c) := ih K 𝓚 hK (i + 1) (by omega) c
      obtain ⟨-, δ, hδ, -⟩ := (hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i
      refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker δ (IsNoetherian.noetherian _) ?_⟩
      rw [top_inf_eq, LinearMap.exact_iff.mp hδ, LinearMap.range_eq_map]
      exact hF.fg_top.map _
  intro M _ _ _ _ 𝓜 hM i c
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  have := key (N + 1) M' 𝓜' hM' i (by omega) c
  exact Module.Finite.of_injective (cohomMap f i c) (hRet S N M M' 𝓜 𝓜' f g hgf i c)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreVanish
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

theorem SerreVanish.proof (hExact : CechExact.Statement.{u, max u v})
    (hTop : CechTop.Statement.{u, max u v}) (hFree : SerreFree.Statement.{u, max u v})
    (hPres : GradedPres.Statement.{u, v}) (hLift : GradedULift.Statement.{u, v})
    (hRet : CohomRetract.Statement.{u, v, max u v}) : SerreVanish.Statement.{u, v} := by
  intro S _ _ N

  have key : ∀ (k : ℕ) (M : Type (max u v)) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
      [IsScalarTower S (Poly S N) M] (𝓜 : GradedPMod S N M), Module.Finite (Poly S N) M →
      ∃ c₀ : ℤ, ∀ i, N + 1 ≤ i + k → 1 ≤ i → ∀ c ≥ c₀, Subsingleton (cohom 𝓜 i c) := by
    intro k
    induction k with
    | zero =>
      intro M _ _ _ _ 𝓜 _
      exact ⟨0, fun i hi _ c _ => hTop S N M 𝓜 i c (by omega)⟩
    | succ k ih =>
      intro M _ _ _ _ 𝓜 hM
      obtain ⟨F, _, _, _, _, K, _, _, _, _, 𝓕, 𝓚, r, b, d, f, g, hb, hK, hf, hg, hfg⟩ :=
        hPres S N M 𝓜 hM
      obtain ⟨c₁, hc₁⟩ := ih K 𝓚 hK
      refine ⟨max c₁ (∑ j, |d j|), fun i hi hi1 c hc => ?_⟩
      have hdc : ∀ j, d j ≤ c := fun j =>
        ((le_abs_self (d j)).trans (Finset.single_le_sum (fun j _ => abs_nonneg (d j))
          (Finset.mem_univ j))).trans ((le_max_right _ _).trans hc)
      have hF := ((hFree S N F 𝓕 r b d hb).2 c hdc).1 i hi1
      have hKv := hc₁ (i + 1) (by omega) (by omega) c ((le_max_left _ _).trans hc)
      obtain ⟨δ, hδ, -⟩ := ((hExact S N K F M 𝓚 𝓕 𝓜 f g hf hg hfg c).2 i).2
      refine ⟨fun x y => ?_⟩
      have hx : ∀ z : cohom 𝓜 i c, z = 0 := fun z => by
        obtain ⟨w, hw⟩ := (hδ z).mp (Subsingleton.elim _ _)
        rw [← hw, Subsingleton.elim w 0, map_zero]
      rw [hx x, hx y]
  intro M _ _ _ _ 𝓜 hM
  obtain ⟨M', _, _, _, _, 𝓜', f, g, hgf, hfg⟩ := hLift S N M 𝓜
  have hM' : Module.Finite (Poly S N) M' :=
    Module.Finite.of_surjective f.toLin fun y => ⟨g.toLin y, hfg y⟩
  obtain ⟨c₀, hc₀⟩ := key N M' 𝓜' hM'
  refine ⟨c₀, fun i hi c hc => ?_⟩
  have := hc₀ i (by omega) hi c hc
  exact (hRet S N M M' 𝓜 𝓜' f g hgf i c).subsingleton

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u

theorem SerrePoly.proof (hL : SerrePoly.Laurent.Statement.{u}) (hT : Cech.Transport.Statement.{u, u, u})
    (hC : SerrePoly.LaurentCohom.Statement.{u}) : SerrePoly.Statement.{u} := by
  intro S _ _ N
  obtain ⟨hinj, hpiece, ι, hι, hres, hmk, hdeg⟩ := hL S N
  obtain ⟨hfin, hvan, hconst⟩ := hC S N
  have hφ : ∀ (I J : StdCell N) (h : I.1 ⊆ J.1) (m : LocMod S N (Poly S N) I.1),
      ι J (locResS I J h m) = Cech.idRes S (Laurent S N) Finset.univ I J h (ι I m) :=
    fun I J h m => hres I J h m
  have hd : ∀ (c : ℤ) (I : StdCell N) (m : LocMod S N (Poly S N) I.1),
      m ∈ degLoc (polyGraded S N) c I → ι I m ∈ laurentDeg S N c I := fun c I m hm => by
    rw [← hdeg c I]; exact Submodule.mem_map_of_mem hm
  have hb : ∀ (i : ℕ) (c : ℤ), Function.Bijective
      (Cech.mapHdeg (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ (hd c) i) :=
    fun i c => hT (N + 1) Finset.univ S _ _ _ _ (degLoc (polyGraded S N) c) (laurentDeg S N c) ι hφ
      (hd c) hι (hdeg c) i
  let E : ∀ (i : ℕ) (c : ℤ), cohom (polyGraded S N) i c ≃ₗ[S] laurentCohom S N i c :=
    fun i c => LinearEquiv.ofBijective _ (hb i c)
  refine ⟨fun i c => Module.Finite.equiv (E i c).symm, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have := hvan c hc i hi
    exact (E i c).toEquiv.subsingleton
  ·
    intro m m' hmm
    have h0 : (constCochain (S := S) (N := N) (M := Poly S N) (m : Poly S N)) =
        constCochain (S := S) (N := N) (M := Poly S N) (m' : Poly S N) := by
      have hmem := (Submodule.Quotient.eq _).mp hmm
      change _ ∈ (⊥ : Submodule S _).comap _ at hmem
      rw [Submodule.mem_comap, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
    let I0 : Cech.Idx (Finset.univ : Finset (Fin (N + 1))) 0 :=
      ⟨⟨{0}, Finset.singleton_nonempty _, Finset.subset_univ _⟩, Finset.card_singleton _⟩
    have h1 := congrArg (ι I0.1) (congrFun h0 I0)
    change ι I0.1 (locMk (Poly S N) I0.1.1 m) = ι I0.1 (locMk (Poly S N) I0.1.1 m') at h1
    rw [hmk, hmk] at h1
    exact Subtype.ext (hinj h1)
  ·
    intro y
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hw : (Cech.mapC ι 0 (z : Cech.Cochain (locSys S N (Poly S N)) 0)) ∈
        Cech.cocyDeg (fun _ : StdCell N => Laurent S N) (laurentDeg S N c)
          (Cech.idRes S (Laurent S N) Finset.univ) 0 := by
      refine Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr ?_, fun I _ => ?_⟩
      · rw [← Cech.mapC_d ι hφ, LinearMap.mem_ker.mp (Submodule.mem_inf.mp z.2).1, map_zero]
      · exact hd c I.1 _ ((Submodule.mem_inf.mp z.2).2 I (Set.mem_univ _))
    obtain ⟨f, hf, hzf⟩ := hconst c hc _ hw
    rw [← hpiece c] at hf
    obtain ⟨m, hm, rfl⟩ := hf
    refine ⟨⟨m, hm⟩, ?_⟩
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    congr 1
    apply Subtype.ext
    funext I
    apply hι I.1
    change ι I.1 (locMk (Poly S N) I.1.1 m) = _
    rw [hmk]
    exact (hzf I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDegLocExact
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v

namespace DegLocExact

theorem decompose_map {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i) (a : A) (k : ι) :
    φ (DirectSum.decompose 𝒜 a k) = DirectSum.decompose ℬ (φ a) k := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp [h0]
  | @homogeneous i m =>
    obtain ⟨m, hm⟩ := m
    by_cases hik : i = k
    · subst hik
      rw [DirectSum.decompose_of_mem_same (ℳ := 𝒜) hm,
        DirectSum.decompose_of_mem_same (ℳ := ℬ) (hφ _ _ hm)]
    · rw [DirectSum.decompose_of_mem_ne (ℳ := 𝒜) hm hik,
        DirectSum.decompose_of_mem_ne (ℳ := ℬ) (hφ _ _ hm) hik, h0]
  | add m m' hm hm' => simp [hadd, DirectSum.decompose_add, hm, hm']

theorem mem_of_map_mem {ι R A B : Type*} [DecidableEq ι] [Semiring R] [AddCommMonoid A] [Module R A]
    [AddCommMonoid B] [Module R B] (𝒜 : ι → Submodule R A) (ℬ : ι → Submodule R B)
    [DirectSum.Decomposition 𝒜] [DirectSum.Decomposition ℬ] (φ : A → B) (h0 : φ 0 = 0)
    (hadd : ∀ a b, φ (a + b) = φ a + φ b) (hφ : ∀ i a, a ∈ 𝒜 i → φ a ∈ ℬ i)
    (hinj : Function.Injective φ) {a : A} {k : ι} (ha : φ a ∈ ℬ k) : a ∈ 𝒜 k := by
  have h := decompose_map 𝒜 ℬ φ h0 hadd hφ a k
  rw [DirectSum.decompose_of_mem_same (ℳ := ℬ) ha] at h
  rw [← hinj h]
  exact SetLike.coe_mem _

variable {S : Type u} [CommRing S] {N : ℕ} {M : Type v} [AddCommGroup M] [Module (Poly S N) M]
  [Module S M] [IsScalarTower S (Poly S N) M]

theorem exists_frac (𝓜 : GradedPMod S N M) (c : ℤ) (I : StdCell N) (z : LocMod S N M I.1)
    (hz : z ∈ degLoc 𝓜 c I) :
    ∃ (m : M) (s : monos (S := S) I.1) (e : ℕ), (s : Poly S N).IsHomogeneous e ∧
      m ∈ 𝓜.piece (c + e) ∧ z = (LocalizedModule.mk m s : LocalizedModule (monos (S := S) I.1) M) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, s, a, e, hm, hs, hae, rfl⟩ := hz
    exact ⟨m, s, e, hs, by rwa [← hae, sub_add_cancel], rfl⟩
  | zero => exact ⟨0, 1, 0, isHomogeneous_one _ _, zero_mem _, (LocalizedModule.zero_mk _).symm⟩
  | add x y _ _ hx hy =>
    obtain ⟨m1, s1, e1, hs1, hm1, rfl⟩ := hx
    obtain ⟨m2, s2, e2, hs2, hm2, rfl⟩ := hy
    refine ⟨(s2 : Poly S N) • m1 + (s1 : Poly S N) • m2, s1 * s2, e1 + e2,
      by simpa using hs1.mul hs2, add_mem ?_ ?_, LocalizedModule.mk_add_mk⟩
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e1 + e2 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e2 _ _ m1 hs2 hm1
    · have h : c + ((e1 + e2 : ℕ) : ℤ) = c + e2 + e1 := by push_cast; ring
      rw [h]; exact 𝓜.smul_mem e1 _ _ m2 hs1 hm2
  | smul r x _ hx =>
    obtain ⟨m, s, e, hs, hm, rfl⟩ := hx
    refine ⟨r • m, s, e, hs, Submodule.smul_mem _ r hm, ?_⟩
    change algebraMap S (Poly S N) r • (LocalizedModule.mk m s : LocalizedModule _ M) = _
    rw [LocalizedModule.smul'_mk, algebraMap_smul]

theorem proof : DegLocExact.Statement := by
  intro S _ N M' M M'' _ _ _ _ _ _ _ _ _ _ _ _ 𝓜' 𝓜 𝓜'' f g hf hg hfg c I
  let _ := 𝓜'.isInternal.chooseDecomposition
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := 𝓜''.isInternal.chooseDecomposition
  refine ⟨fun z hz hz0 => ?_, fun z hz => ?_⟩
  · obtain ⟨m, s, e, hs, hm, rfl⟩ := exists_frac 𝓜 c I z hz
    rw [locMap_mk] at hz0
    have h0 : (LocalizedModule.mk (g.toLin m) s : LocalizedModule (monos (S := S) I.1) M'') =
        LocalizedModule.mk 0 s := by rw [LocalizedModule.zero_mk]; exact hz0
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 h0
    set T : monos (S := S) I.1 := u * s with hT
    obtain ⟨e', he'⟩ := monos_isHomogeneous T.2
    have hgT : g.toLin ((T : Poly S N) • m) = 0 := by
      rw [map_smul, hT, Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← Submonoid.smul_def,
        hu, smul_zero, smul_zero]
    obtain ⟨m', hm'⟩ := (hfg _).1 hgT
    have hTm : (T : Poly S N) • m ∈ 𝓜.piece (c + e + e') := 𝓜.smul_mem e' _ _ m he' hm
    have hm'd : m' ∈ 𝓜'.piece (c + e + e') :=
      mem_of_map_mem 𝓜'.piece 𝓜.piece f.toLin (map_zero _) (map_add _) f.map_piece hf (hm' ▸ hTm)
    refine ⟨LocalizedModule.mk m' (T * s), Submodule.subset_span
      ⟨m', T * s, c + e + e', e' + e, hm'd, by simpa using he'.mul hs, by push_cast; ring, rfl⟩, ?_⟩
    rw [locMap_mk, hm', ← Submonoid.smul_def, LocalizedModule.mk_cancel_common_left]
  · obtain ⟨m'', s, e, hs, hm'', rfl⟩ := exists_frac 𝓜'' c I z hz
    obtain ⟨m, rfl⟩ := hg m''
    refine ⟨LocalizedModule.mk (DirectSum.decompose 𝓜.piece m (c + e) : M) s, Submodule.subset_span
      ⟨_, s, c + e, e, SetLike.coe_mem _, hs, by ring, rfl⟩, ?_⟩
    rw [locMap_mk, decompose_map 𝓜.piece 𝓜''.piece g.toLin (map_zero _) (map_add _) g.map_piece,
      DirectSum.decompose_of_mem_same (ℳ := 𝓜''.piece) hm'']

end DegLocExact

end

end GroundTheory.Heights₂.Heights.Kleiman
end
