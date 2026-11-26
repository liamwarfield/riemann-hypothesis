module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleCechObj
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsStepThreeOnWGen
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StatementsVeryAmpleZFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open Filter

noncomputable section

universe u v w

def VeryAmpleZExtend.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ, c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H 1 (h j) I) →
      ∀ f ∈ F.sub K, ∀ᶠ M in atTop, c ^ M • f ∈ secsOnZ F.toSubSystem H h J

def VeryAmpleZChartSpan.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω), (∀ l, h l ∈ H.secs) →
    ∀ (I : Chart x) (J : Chart h) (g : Finset E), F.sub I ≤ Submodule.span (chartRing S x I) (g : Set E) →
      ∀ e ∈ secsOnZChart F H h I J, ∃ β : E → Ω,
        (∀ y ∈ g, β y ∈ ampleChart H J.1.card (xProd J) I) ∧ e = ∑ y ∈ g, β y • y

def VeryAmpleZChartRing.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω), IsVeryAmpleBy H.toSubSystem h →
    ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ c ∈ ampleRing H.toSubSystem 1 (h j), ∀ K : Chart x,
      (∀ I : Chart x, ∃ e : ℕ,
        c ^ e * (xProd I ^ K.1.card / xProd K ^ I.1.card) ∈ ampleChart H.toSubSystem 1 (h j) I) →
      ∀ α ∈ ampleChart H.toSubSystem J.1.card (xProd J) K, ∀ᶠ M in atTop, c ^ M * α ∈ chartRing S h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SnapperHyperplaneMidSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

def SnapperHyperplaneMid.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
    primeOf (S := k) x ≤ pp → ∀ i : Fin (N + 1), (X i : Poly k N) ∉ pp →
    ∀ (a : ℤ) (t : ℕ) (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ),
      eulerCharQuot k
          ((((twistSys k x (a + 1)).twist (idealSys x (pp ⊔ Ideal.span {(X i : Poly k N)}))).twistPows t
            (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
          ((((twistSys k x (a + 1)).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
            (twistSys k x c)) =
        pieceChar k pp a L n c

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

section Helpers

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem twistPows_twist_comm (F Q : SubSystem S x Ω) :
    ∀ (t : ℕ) (L : Fin t → SubSystem S x Ω) (n : Fin t → ℕ),
      (F.twist Q).twistPows t L n = (F.twistPows t L n).twist Q
  | 0, _, _ => rfl
  | t + 1, L, n => by
    simp only [SubSystem.twistPows]
    rw [twistPows_twist_comm F Q t, SubSystem.twist_assoc, SubSystem.twist_comm Q, ← SubSystem.twist_assoc]

def twistPowsBundle (F : LineBundle S x) :
    (t : ℕ) → (Fin t → LineBundle S x) → (Fin t → ℕ) → LineBundle S x
  | 0, _, _ => F
  | t + 1, L, n => (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).tensorProd
      ((L (Fin.last t)).powBundle (n (Fin.last t)))

theorem twistPowsBundle_toSubSystem (F : LineBundle S x) :
    ∀ (t : ℕ) (L : Fin t → LineBundle S x) (n : Fin t → ℕ),
      (twistPowsBundle F t L n).toSubSystem = F.toSubSystem.twistPows t (fun j => (L j).toSubSystem) n
  | 0, _, _ => rfl
  | t + 1, L, n => by
    change (twistPowsBundle F t (fun j => L j.castSucc) (fun j => n j.castSucc)).toSubSystem.twist
      ((L (Fin.last t)).powBundle (n (Fin.last t))).toSubSystem = _
    rw [twistPowsBundle_toSubSystem F t, LineBundle.powBundle_toSubSystem]
    rfl

theorem idealMod_le_one (J : Ideal (Poly S N)) (I : Chart x) : idealMod J I ≤ 1 := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
  exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩

theorem idealMod_le_of_le {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    idealMod J I ≤ idealMod J' I :=
  Submodule.span_mono fun _ ⟨f, s, e, hf, hs, hfe, hse, hz⟩ => ⟨f, s, e, h hf, hs, hfe, hse, hz⟩

theorem twist_idealSys_sub_le (Q : SubSystem S x Ω) (J : Ideal (Poly S N)) (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ Q.sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line]
  exact (Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_one J I ha) hb).trans (one_mul _).le

theorem twist_idealSys_sub_mono (Q : SubSystem S x Ω) {J J' : Ideal (Poly S N)} (h : J ≤ J') (I : Chart x) :
    (Q.twist (idealSys x J)).sub I ≤ (Q.twist (idealSys x J')).sub I := by
  rw [SubSystem.twist_sub_eq_mul_of_line, SubSystem.twist_sub_eq_mul_of_line]
  exact Submodule.mul_le.mpr fun a ha b hb => Submodule.mul_mem_mul (idealMod_le_of_le h I ha) hb

end Helpers

theorem sup_span_X_homogeneous {R : Type u} [CommRing R] {N : ℕ} (pp : Ideal (Poly R N))
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (i : Fin (N + 1)) :
    ∀ f ∈ pp ⊔ Ideal.span {(X i : Poly R N)}, ∀ d : ℕ,
      homogeneousComponent d f ∈ pp ⊔ Ideal.span {(X i : Poly R N)} := by
  intro f hf d
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  rw [map_add (f := _)]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (hh g hg d)) (Ideal.mem_sup_right ?_)
  have hspan := IdealTwistFamily.homogeneousComponent_mul_form r (X i) (isHomogeneous_X R i) d
  refine (Submodule.span_le.mpr ?_ : _ ≤ (Ideal.span {(X i : Poly R N)}).restrictScalars R) hspan
  rintro _ ⟨z, d', -, -, rfl⟩
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem SnapperHyperplane.proof (hA : SnapperQuotAdd.Statement.{u, w, w})
    (hD : SnapperQuotDevissage.Statement.{u, w, w}) (hM : SnapperHyperplaneMid.Statement.{u, w}) :
    SnapperHyperplane.Statement.{u, w} := by
  intro k _ Ω _ _ N x pp hp hh hle i hi a
  set J : Ideal (Poly k N) := pp ⊔ Ideal.span {(X i : Poly k N)} with hJdef
  let B := twistBundle k x (a + 1)
  let F₂ : SubFamily k x Ω :=
    { B.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff B J }
  obtain ⟨r, qq, b, hqq, heq⟩ := hD k Ω N x Ω B.toSubFamily F₂ B.fg
    (fun I => twist_idealSys_sub_le B.toSubSystem J I) J (sup_span_X_homogeneous pp hh i)
    (hle.trans le_sup_left) (fun I => le_rfl)
  refine ⟨r, qq, b, fun m => ⟨(hqq m).1, (hqq m).2.1, le_sup_left.trans (hqq m).2.2,
    (hqq m).2.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩, fun t L n c => ?_⟩
  let Q := (twistPowsBundle B t L n).tensorProd (twistBundle k x c)
  have hQ : Q.toSubSystem =
      ((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c) := by
    change (twistPowsBundle B t L n).toSubSystem.twist (twistSys k x c) = _
    rw [twistPowsBundle_toSubSystem]
    rfl
  have hG : ∀ K : Ideal (Poly k N),
      (((twistSys k x (a + 1)).twist (idealSys x K)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c) = Q.toSubSystem.twist (idealSys x K) := by
    intro K
    rw [hQ, twistPows_twist_comm (twistSys k x (a + 1)) (idealSys x K), SubSystem.twist_assoc,
      SubSystem.twist_comm (idealSys x K), ← SubSystem.twist_assoc]
  let G₂ : SubFamily k x Ω := { Q.twist (idealSys x J) with mem_iff := IdealTwistFamily.twist_mem_iff Q J }
  let G₃ : SubFamily k x Ω := { Q.twist (idealSys x pp) with mem_iff := IdealTwistFamily.twist_mem_iff Q pp }
  have hadd : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) +
        eulerCharQuot k (Q.toSubSystem.twist (idealSys x J)) (Q.toSubSystem.twist (idealSys x pp)) :=
    hA k Ω N x Ω Q.toSubFamily G₂ G₃ Q.fg (fun I => twist_idealSys_sub_le Q.toSubSystem J I)
      (fun I => twist_idealSys_sub_mono Q.toSubSystem le_sup_left I)
  have h1 : pieceChar k pp a L n (c + 1) =
      eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x pp)) := by
    have eA : ((twistSys k x a).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x (c + 1)) =
        Q.toSubSystem := by
      rw [hQ, ← twistSys_twist_eq_add a 1,
        twistPows_twist_comm (twistSys k x a) (twistSys k x 1), SubSystem.twist_assoc,
        twistSys_twist_eq_add, add_comm 1 c]
    have eB : (((twistSys k x a).twist (idealSys x pp)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x (c + 1)) = Q.toSubSystem.twist (idealSys x pp) := by
      rw [← hG pp, ← twistSys_twist_eq_add a 1, SubSystem.twist_assoc (twistSys k x a),
        SubSystem.twist_comm (twistSys k x 1), ← SubSystem.twist_assoc (twistSys k x a),
        twistPows_twist_comm ((twistSys k x a).twist (idealSys x pp)) (twistSys k x 1),
        SubSystem.twist_assoc _ (twistSys k x 1), twistSys_twist_eq_add, add_comm 1 c]
    unfold pieceChar
    rw [eA, eB]
  have h2 : eulerCharQuot k Q.toSubSystem (Q.toSubSystem.twist (idealSys x J)) =
      ∑ m, pieceChar k (qq m) (b m) L n c := by
    have := heq t L n c
    change eulerCharQuot k
      (((twistSys k x (a + 1)).twistPows t (fun j => (L j).toSubSystem) n).twist (twistSys k x c))
      ((((twistSys k x (a + 1)).twist (idealSys x J)).twistPows t (fun j => (L j).toSubSystem) n).twist
        (twistSys k x c)) = _ at this
    rwa [hG J, ← hQ] at this
  have h3 := hM k Ω N x pp hp hh hle i hi a t L n c
  rw [← hJdef, hG J, hG pp] at h3
  rw [h1, hadd, h2, h3]
  ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem eulerCharQuot_self {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubSystem k x E) : eulerCharQuot k F F = 0 := by
  unfold eulerCharQuot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  have h2 : Subsingleton (Cech.Cochain (fun I => F.sub I ⧸ SubSystem.quotSub F F I) i) := by
    unfold Cech.Cochain; infer_instance
  have h3 : Subsingleton (SubSystem.quotH F F i) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  simp [Module.finrank_zero_of_subsingleton]

theorem subSystem_ext {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    {F G : SubSystem k x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by
  obtain ⟨sF, mF⟩ := F
  obtain ⟨sG, mG⟩ := G
  have : sF = sG := funext h
  subst this
  rfl

theorem twist_idealSys_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by
  refine subSystem_ext fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
      isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
  have hle : (idealSys x pp).sub I ≤ 1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
    exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine le_antisymm (Submodule.mul_le.mpr fun q hq y hy => ?_) fun y hy => by
    simpa using Submodule.mul_mem_mul h1 hy
  obtain ⟨q', rfl⟩ := Submodule.mem_one.mp (hle hq)
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ q' hy

theorem pieceChar_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by
  unfold pieceChar
  rw [twist_idealSys_of_irrelevant pp hpp a]
  exact eulerCharQuot_self _

end Lemmas

section Dim

variable {R : Type*} [CommRing R]

theorem ringKrullDim_quotient_succ_le_of_lt {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by
  obtain ⟨r, hrq, hrp⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk pp r ∈ nonZeroDivisors (R ⧸ pp) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk pp r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hrq, mul_zero]
  have := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hker (Ideal.Quotient.factor_surjective h.le))
  gcongr

end Dim

section Induction

variable {k : Type u} [Field k] {N : ℕ}

theorem one_le_ringKrullDim_of_relevant (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by
  obtain ⟨i, hi⟩ := hrel
  have hle : pp ≤ RingHom.ker (constantCoeff : Poly k N →+* k) := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h0
    have h1 := hh f hf 0
    rw [homogeneousComponent_zero] at h1
    have h0' : AddMonoidAlgebra.coeff f 0 ≠ 0 := by rwa [← constantCoeff_eq]
    have hu : IsUnit (C (AddMonoidAlgebra.coeff f 0) : Poly k N) := (isUnit_iff_ne_zero.mpr h0').map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  have hlt : pp < RingHom.ker (constantCoeff : Poly k N →+* k) :=
    lt_of_le_of_ne hle fun h => hi (h ▸ by simp [RingHom.mem_ker])
  have hnt : Nontrivial (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
    _ ≤ ringKrullDim (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) + 1 :=
        by gcongr; exact ringKrullDim_nonneg_of_nontrivial
    _ ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_quotient_succ_le_of_lt hlt

theorem withBot_le_of_succ_le {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + 1 ≤ (D : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

theorem isNumPolyLT_sum {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by
  choose Q hQ hev using h
  refine ⟨∑ m, Q m, ?_, fun n c => by simp [hev, map_sum]⟩
  rcases Nat.eq_zero_or_pos D with hD | hD
  · left
    subst hD
    exact Finset.sum_eq_zero fun m _ => (hQ m).resolve_right (Nat.not_lt_zero _)
  · right
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hD)]
    intro m _
    rcases hQ m with h0 | h0
    · rw [h0, totalDegree_zero]; exact hD
    · exact h0

theorem IsNumPolyLT.congr {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by
  obtain ⟨Q, hQ, hev⟩ := h
  exact ⟨Q, hQ, fun n c => (hfg n c).symm.trans (hev n c)⟩

variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}

theorem pieceChar_isNumPolyLT (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by
  induction D with
  | zero =>
    intro pp hp hh _ hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have := (one_le_ringKrullDim_of_relevant pp hh hrel).trans hdim
      exact absurd this (by simp)
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
  | succ D ih =>
    intro pp hp hh hle hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have key : ∀ (qq : Ideal (Poly k N)) (b : ℤ), qq.IsPrime →
          (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) → pp < qq →
          IsNumPolyLT t D (fun n c => (pieceChar k qq b L n c : ℚ)) := fun qq b hq hqh hlt =>
        ih qq hq hqh (hle.trans hlt.le)
          (withBot_le_of_succ_le ((ringKrullDim_quotient_succ_le_of_lt hlt).trans hdim)) b
      obtain ⟨i, hi⟩ := hrel
      obtain ⟨r, qq, b, hqq, heq⟩ := hH k Ω N x pp hp hh hle i hi a
      have h0 : IsNumPolyLT t D
          (fun n c => (pieceChar k pp a L n (c + 1) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        (isNumPolyLT_sum _ fun m => key (qq m) (b m) (hqq m).1 (hqq m).2.1
          (lt_of_le_of_ne (hqq m).2.2.1 fun h => hi (h ▸ (hqq m).2.2.2))).congr
          fun n c => by exact_mod_cast (heq t L n c).symm
      choose μ r' qq' b' hqq' heq' using fun j => hS k Ω N x pp hp hh hle ⟨i, hi⟩ t L j a
      have hj : ∀ j, IsNumPolyLT t D (fun n c =>
          (pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ j) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        fun j => (isNumPolyLT_sum _ fun m => key (qq' j m) (b' j m) (hqq' j m).1 (hqq' j m).2.1
          (hqq' j m).2.2).congr fun n c => by exact_mod_cast (heq' j n c).symm
      exact hP t D (fun n c => (pieceChar k pp a L n c : ℚ)) μ h0 hj
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩

end Induction

theorem Snapper.proof (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x e hZ E _ _ _ _ F hF t L
  obtain ⟨r, pp, a, hpp, heq⟩ := hD k Ω N x E F hF
  have hdim : ∀ m, ringKrullDim (Poly k N ⧸ pp m) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := fun m =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (hpp m).2.2)).trans hZ.dim.le
  obtain ⟨Q, hQ, hev⟩ := isNumPolyLT_sum (fun m n c => (pieceChar k (pp m) (a m) L n c : ℚ))
    fun m => pieceChar_isNumPolyLT hH hS hP L (e + 1) (pp m) (hpp m).1 (hpp m).2.1 (hpp m).2.2 (hdim m) (a m)
  refine ⟨Q, ?_, fun n c => ?_⟩
  · rcases hQ with h0 | h0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  · rw [heq t L n c, ← hev n c]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial
open scoped Pointwise

noncomputable section

universe u w

namespace GraphClosedAlt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

theorem mem_sub_of_mem_secs' {F : SubSystem S x Ω} {z : Ω} (hz : z ∈ F.secs) (I : Chart x) :
    z ∈ F.sub I := by
  rw [SubSystem.secs, Submodule.mem_iInf] at hz
  exact hz I

theorem exists_fin_generators (G : LineBundle S x) (hG : G.toSubSystem.Generated) :
    ∃ (r : ℕ) (g : Fin (r + 1) → Ω), (∀ a, g a ∈ G.toSubSystem.secs) ∧
      ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I := by
  classical
  have hloc : ∀ I : Chart x, ∃ F : Finset Ω, (F : Set Ω) ⊆ G.toSubSystem.secs ∧
      G.sub I ≤ Submodule.span (chartRing S x I) (F : Set Ω) := by
    intro I
    obtain ⟨t, ht⟩ := G.fg I
    have hy : ∀ y : Ω, ∃ T : Finset Ω, (T : Set Ω) ⊆ G.toSubSystem.secs ∧
        (y ∈ G.sub I → y ∈ Submodule.span (chartRing S x I) (T : Set Ω)) := by
      intro y
      by_cases hyI : y ∈ G.sub I
      · have : y ∈ Submodule.span (chartRing S x I) (G.toSubSystem.secs : Set Ω) := by
          rw [hG I]; exact hyI
        obtain ⟨T, hT, hyT⟩ := Submodule.mem_span_finite_of_mem_span this
        exact ⟨T, hT, fun _ => hyT⟩
      · exact ⟨∅, by simp, fun h => absurd h hyI⟩
    choose T hT hTy using hy
    refine ⟨t.biUnion T, ?_, ?_⟩
    · intro z hz
      obtain ⟨y, -, hzy⟩ := Finset.mem_biUnion.mp hz
      exact hT y hzy
    · rw [← ht, Submodule.span_le]
      intro y hyt
      have hyI : y ∈ G.sub I := by rw [← ht]; exact Submodule.subset_span hyt
      exact Submodule.span_mono (by
        intro z hz
        exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨y, hyt, hz⟩)) (hTy y hyI)
  choose F hF hFI using hloc
  set A := Finset.univ.biUnion F
  let g : Fin (A.card + 1) → Ω := Fin.cons 0 fun i => (A.equivFin.symm i : Ω)
  have hrange : Set.range g = insert 0 (A : Set Ω) := by
    simp only [g, Fin.range_cons]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩; exact (A.equivFin.symm i).2
    · intro hy; exact ⟨A.equivFin ⟨y, hy⟩, by simp⟩
  have hA : (A : Set Ω) ⊆ G.toSubSystem.secs := by
    intro z hz
    obtain ⟨I, -, hzI⟩ := Finset.mem_biUnion.mp hz
    exact hF I hzI
  refine ⟨A.card, g, fun a => ?_, fun I => le_antisymm ?_ ?_⟩
  · have : g a ∈ insert 0 (A : Set Ω) := hrange ▸ Set.mem_range_self a
    rcases this with h0 | hA'
    · rw [h0]; exact Submodule.zero_mem _
    · exact hA hA'
  · rw [Submodule.span_le, hrange]
    rintro z (rfl | hz)
    · exact Submodule.zero_mem _
    · exact mem_sub_of_mem_secs' (hA hz) I
  · refine (hFI I).trans (Submodule.span_mono ?_)
    rw [hrange]
    intro z hz
    exact Set.mem_insert_of_mem _ (Finset.mem_coe.mpr
      (Finset.mem_biUnion.mpr ⟨I, Finset.mem_univ I, Finset.mem_coe.mp hz⟩))

theorem twist_pow_sub (G H : SubSystem S x Ω) (n : ℕ) (I : Chart x) :
    ((G.twist H).pow n).sub I = (H.sub I * G.sub I) ^ n := by
  rw [SubSystem.pow_sub, SubSystem.twist_sub_eq_mul_of_line]

theorem ampleChart_twist (G H : SubSystem S x Ω) {h g : Ω} (I : Chart x) (hg : g ∈ G.sub I) {u : Ω}
    (hu : u ∈ ampleChart H 1 h I) : u ∈ ampleChart (G.twist H) 1 (h * g) I := by
  obtain ⟨n, hn⟩ := hu
  refine ⟨n, ?_⟩
  rw [one_mul] at hn ⊢
  rw [SubSystem.pow_sub] at hn
  rw [twist_pow_sub, mul_pow]
  have : u * (h * g) ^ n = (u * h ^ n) * g ^ n := by ring
  rw [this]
  exact Submodule.mul_mem_mul hn (Submodule.pow_mem_pow _ hg n)

theorem ampleRing_twist (G H : SubSystem S x Ω) {h g : Ω} (hg : g ∈ G.secs) {u : Ω}
    (hu : u ∈ ampleRing H 1 h) : u ∈ ampleRing (G.twist H) 1 (h * g) :=
  Set.mem_iInter.mpr fun I =>
    ampleChart_twist G H I (mem_sub_of_mem_secs' hg I) (Set.mem_iInter.mp hu I)

theorem ampleRing_twist_subset (G H : SubSystem S x Ω) {r₁ r₂ : ℕ} (g : Fin (r₁ + 1) → Ω)
    (h : Fin (r₂ + 1) → Ω)
    (hgI : ∀ I, Submodule.span (chartRing S x I) (Set.range g) = G.sub I) (hh : IsVeryAmpleBy H h)
    {b₀ : Fin (r₁ + 1)} {l₀ : Fin (r₂ + 1)} (hne : h l₀ * g b₀ ≠ 0) (T : Subalgebra S Ω)
    (hT : ∀ b m, h m * g b / (h l₀ * g b₀) ∈ T) :
    ampleRing (G.twist H) 1 (h l₀ * g b₀) ⊆ T := by
  classical
  set p := h l₀ * g b₀ with hp
  have hl₀ : h l₀ ≠ 0 := left_ne_zero_of_mul hne
  have hb₀ : g b₀ ≠ 0 := right_ne_zero_of_mul hne
  have hB : ampleRing H 1 (h l₀) ⊆ T := by
    intro y hy
    have hy' := hh.closed l₀ hl₀ hy
    refine (Algebra.adjoin_le ?_ : ampleBase (S := S) h l₀ ≤ T) hy'
    rintro _ ⟨m, rfl⟩
    have : h m / h l₀ = h m * g b₀ / p := by rw [hp, mul_div_mul_right _ _ hb₀]
    show h m / h l₀ ∈ T
    rw [this]; exact hT b₀ m
  have hPn : ∀ n : ℕ, ∀ t ∈ (Set.range h * Set.range g) ^ n, t / p ^ n ∈ T := by
    intro n
    induction n with
    | zero =>
      intro t ht
      rw [pow_zero, Set.mem_one] at ht
      rw [ht, pow_zero, div_one]; exact one_mem T
    | succ n ih =>
      intro t ht
      rw [pow_succ, Set.mem_mul] at ht
      obtain ⟨t₁, ht₁, t₂, ht₂, rfl⟩ := ht
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp ht₂
      have : t₁ * (h m * g b) / p ^ (n + 1) = (t₁ / p ^ n) * (h m * g b / p) := by
        rw [pow_succ, mul_div_mul_comm]
      rw [this]
      exact mul_mem (ih t₁ ht₁) (hT b m)
  obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine l₀ hl₀
  intro y hy
  have hloc : ∀ k, ∃ e : ℕ, b k ^ e * y ∈ T := by
    intro k
    obtain ⟨n', hn'⟩ := Set.mem_iInter.mp hy (J k)
    rw [one_mul, twist_pow_sub, ← hgI (J k), ← hh.generates (J k), Submodule.span_mul_span,
      Submodule.span_pow] at hn'
    have hbT : b k ∈ T := hB (hb k)
    suffices hQ : ∀ z ∈ Submodule.span (chartRing S x (J k)) ((Set.range h * Set.range g) ^ n'),
        ∃ e : ℕ, b k ^ e * (z / p ^ n') ∈ T by
      obtain ⟨e, he⟩ := hQ _ hn'
      rw [mul_div_cancel_right₀ _ (pow_ne_zero _ hne)] at he
      exact ⟨e, he⟩
    intro z hz
    induction hz using Submodule.span_induction with
    | mem t ht => exact ⟨0, by rw [pow_zero, one_mul]; exact hPn n' t ht⟩
    | zero => exact ⟨0, by rw [zero_div, mul_zero]; exact zero_mem T⟩
    | add z₁ z₂ _ _ h₁ h₂ =>
      obtain ⟨e₁, he₁⟩ := h₁
      obtain ⟨e₂, he₂⟩ := h₂
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * ((z₁ + z₂) / p ^ n') =
          b k ^ e₂ * (b k ^ e₁ * (z₁ / p ^ n')) + b k ^ e₁ * (b k ^ e₂ * (z₂ / p ^ n')) := by
        rw [pow_add, add_div]; ring
      rw [this]
      exact add_mem (mul_mem (pow_mem hbT _) he₁) (mul_mem (pow_mem hbT _) he₂)
    | smul c z _ hz =>
      obtain ⟨e₂, he₂⟩ := hz
      obtain ⟨e₁, he₁⟩ := exists_pow_mul_mem_ampleRing H (h l₀) (b k) (J k) (hb k) (hJ k) c.2
      refine ⟨e₁ + e₂, ?_⟩
      have : b k ^ (e₁ + e₂) * (c • z / p ^ n') = (b k ^ e₁ * c) * (b k ^ e₂ * (z / p ^ n')) := by
        rw [chartRing_smul_def, pow_add]; ring
      rw [this]
      exact mul_mem (hB he₁) he₂
  choose e he using hloc
  let bT : Fin n → T := fun k => ⟨b k, hB (hb k)⟩
  have htop : Ideal.span (Set.range bT) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : T) = ∑ k, (⟨a k, hB (ha k)⟩ : T) * bT k := by
      apply Subtype.ext
      simp only [bT]
      push_cast
      exact hsum.symm
    rw [h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)
  set E := ∑ k, e k
  have h1 : (1 : T) ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT) := by
    rw [Ideal.span_pow_eq_top _ htop E]; trivial
  suffices hP : ∀ t ∈ Ideal.span ((fun z : T => z ^ E) '' Set.range bT), (t : Ω) * y ∈ T by
    simpa using hP 1 h1
  intro t ht
  induction ht using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := hz
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ k))
    have : ((bT k ^ E : T) : Ω) * y = b k ^ d * (b k ^ e k * y) := by
      simp only [SubmonoidClass.coe_pow, bT]
      rw [show E = e k + d from hd, pow_add]; ring
    rw [this]
    exact mul_mem (pow_mem (hB (hb k)) _) (he k)
  | zero => simp
  | add t₁ t₂ _ _ h₁ h₂ =>
    rw [Subalgebra.coe_add, add_mul]; exact add_mem h₁ h₂
  | smul c t _ ht =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_assoc]; exact mul_mem c.2 ht

end GraphClosedAlt


open GraphClosedAlt in
theorem GraphClosed.proof : GraphClosed.Statement.{u, w} := by
  intro k _ Ω _ _ N x G H hG hH
  obtain ⟨r₁, g, hg, hgI⟩ := exists_fin_generators G hG
  obtain ⟨r₂, h, hh⟩ := hH
  have hr : (r₁ + 1) * (r₂ + 1) = (r₁ * r₂ + r₁ + r₂) + 1 := by ring
  let E : Fin (r₁ + 1) × Fin (r₂ + 1) ≃ Fin (r₁ * r₂ + r₁ + r₂ + 1) :=
    finProdFinEquiv.trans (finCongr hr)
  let pr : Fin (r₁ + 1) × Fin (r₂ + 1) → Ω := fun q => h q.2 * g q.1
  let s : Fin (r₁ * r₂ + r₁ + r₂ + 1) → Ω := fun j => pr (E.symm j)
  have hs : ∀ j, s j = h (E.symm j).2 * g (E.symm j).1 := fun j => rfl
  have hsE : ∀ b m, s (E (b, m)) = h m * g b := fun b m => by simp [s, pr]
  have hrange : Set.range s = Set.range h * Set.range g := by
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact Set.mem_mul.mpr ⟨_, ⟨(E.symm j).2, rfl⟩, _, ⟨(E.symm j).1, rfl⟩, (hs j).symm⟩
    · intro hz
      obtain ⟨_, ⟨m, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ := Set.mem_mul.mp hz
      exact ⟨E (b, m), hsE b m⟩
  refine ⟨r₁ * r₂ + r₁ + r₂, s, ?_, ?_, ?_, ?_⟩
  · intro j
    rw [hs, SubSystem.secs, Submodule.mem_iInf]
    intro I
    exact Submodule.subset_span ⟨h (E.symm j).2, mem_sub_of_mem_secs' (hh.mem_secs _) I,
      g (E.symm j).1, mem_sub_of_mem_secs' (hg _) I, (smul_eq_mul _ _).symm⟩
  · intro I
    rw [hrange, ← Submodule.span_mul_span, hh.generates I, hgI I,
      SubSystem.twist_sub_eq_mul_of_line]
  · intro j hj
    rw [hs] at hj ⊢
    refine ampleRing_twist_subset G.toSubSystem H.toSubSystem g h hgI hh hj _ fun b m => ?_
    have : h m * g b / (h (E.symm j).2 * g (E.symm j).1) = s (E (b, m)) / s j := by
      rw [hsE, hs]
    rw [this]
    exact Algebra.subset_adjoin ⟨E (b, m), rfl⟩
  · intro j hj
    rw [hs] at hj ⊢
    have hl : h (E.symm j).2 ≠ 0 := left_ne_zero_of_mul hj
    obtain ⟨n, a, b, J, ha, hb, hsum, hJ⟩ := hh.affine _ hl
    refine ⟨n, a, b, J, fun q => ampleRing_twist _ _ (hg _) (ha q),
      fun q => ampleRing_twist _ _ (hg _) (hb q), hsum, fun q I => ?_⟩
    obtain ⟨e, he⟩ := hJ q I
    exact ⟨e, ampleChart_twist _ _ I (mem_sub_of_mem_secs' (hg _) I) he⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFamilySt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFamily.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h →
    ∃ F' : SubFamily S h E, ∀ J, (F'.sub J).restrictScalars S = secsOnZ F.toSubSystem H.toSubSystem h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.SubFamilyTwistPowSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def SubFamilyTwistPow.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (Q : SubFamily S x Ω) (a : ℕ),
    ∃ G : SubFamily S x E, G.toSubSystem = F.twist (Q.pow a)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZChartSmulSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def ZChartSmul.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubSystem S x E) (H : SubSystem S x Ω) (r : ℕ) (h : Fin (r + 1) → Ω),
    (∀ l, h l ∈ H.secs) → ∀ (J : Chart h) (j : Fin (r + 1)), j ∈ J.1 → ∀ (I : Chart x) (a : Ω),
      a ∈ ampleRing H 1 (h j) → ∀ z ∈ secsOnZChart G H h I J, a • z ∈ secsOnZChart G H h I J

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechHdegOfSubSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechHdegOfSub.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (T : SubSystem S x E) (n : ℕ),
    Nonempty (T.H n ≃ₗ[S] Cech.Hdeg (fun _ : Chart x => E) (fun I => (T.sub I).restrictScalars S)
      (Cech.idRes S E (support x)) n)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFiniteSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZFinite.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] [IsNoetherianRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E), (∀ I, (F.sub I).FG) → ∀ (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ J : Chart h, ∃ t : Finset E,
      (t : Set E) ⊆ secsOnZ F.toSubSystem H.toSubSystem h J ∧
      secsOnZ F.toSubSystem H.toSubSystem h J ≤ (Submodule.span (chartRing S h J) (t : Set E)).restrictScalars S

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.KHCombContractSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KHFree

noncomputable section

def KHCombContract.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)] (J : ∀ k, Finset (ι k)) (n : ℕ) (k : K) (i₀ : ι k),
    i₀ ∉ J k → ∀ f : CombC S J n, combD S J n f = 0 →
      ∃ g : CombC S J n, f - g ∈ combB S J n ∧ ∀ I : CombCell ι J n,
        (J k = ∅ ∧ (I.1.1 k).card = 1 →
          ∃ I' : CombCell ι J n, I'.1.1 k = {i₀} ∧ (∀ l, l ≠ k → I'.1.1 l = I.1.1 l) ∧ g I = f I') ∧
        (¬ (J k = ∅ ∧ (I.1.1 k).card = 1) → g I = 0)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZRowsSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZRows.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (G : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ J : Chart h,
      (∀ I I' : Chart x, I.1 ⊆ I'.1 →
        secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I' J) ∧
      Cech.AugExact S (fun I => secsOnZChart G.toSubSystem H.toSubSystem h I J) (secsOnZ G.toSubSystem H.toSubSystem h J)

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZTwistSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def VeryAmpleZTwist.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] [Algebra S Ω] (N : ℕ)
    (x : Fin (N + 1) → Ω) (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]
    (F : SubFamily S x E) (H : LineBundle S x) (r : ℕ) (h : Fin (r + 1) → Ω),
    IsVeryAmpleBy H.toSubSystem h → ∀ (a : ℕ) (J : Chart h),
      (Submodule.span (chartRing S h J) {z | ∃ q ∈ twistMod S h (a : ℤ) J,
          ∃ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J, z = q • y}).restrictScalars S =
        secsOnZ (F.twist (H.pow a)) H.toSubSystem h J

end

end GroundTheory.Heights₂.Heights.Kleiman
end
