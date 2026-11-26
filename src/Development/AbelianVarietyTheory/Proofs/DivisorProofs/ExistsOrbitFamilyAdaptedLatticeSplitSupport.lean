module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpan

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortRuleChangeOfCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FixesDatumOfCongAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

set_option autoImplicit false

namespace GlobalTheory.ShortMove

section Lattices

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem trivAt_of_dvd {Λ : GenLat E n} {a b : ℕ} (h : a ∣ b) (hT : Λ.TrivAt b) : Λ.TrivAt a := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  exact ⟨k, hk.coprime_dvd_right h, h1, h2⟩

theorem entries_of_congAt {b : ℕ} {g : Matrix (Fin n) (Fin n) E} (h : UnRep.CongAt (stdLat E n) b b g) :
    ∃ t : ℕ, t.Coprime b ∧ ∃ w : Fin n → Fin n → 𝓞 E, ∀ i j,
      (t : E) * (g i j - if i = j then 1 else 0) = (b : E) * (w i j : E) := by
  obtain ⟨t, ht, hw⟩ := h
  have h1 : ∀ j : Fin n, (Pi.single j 1 : Fin n → E) ∈ stdLat E n := fun j i _ => by
    refine Submodule.mem_one.2 ?_
    by_cases hij : i = j
    · subst hij; exact ⟨1, by simp⟩
    · exact ⟨0, by simp [hij]⟩
  choose w hw1 hw2 using fun j => hw _ (h1 j)
  choose u hu using fun j i => Submodule.mem_one.1 (hw1 j i (Set.mem_univ _))
  refine ⟨t, ht, fun i j => u j i, fun i j => ?_⟩
  have := congrFun (hw2 j) i
  simp only [Pi.smul_apply, Pi.sub_apply, nsmul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply,
    Pi.single_apply, ← hu] at this
  exact this

end Lattices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem quot_smul {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {I : Ideal R} {a : R} (ha : a ∈ I)
    (q : V ⧸ (I • ⊤ : Submodule R V)) : a • q = 0 := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul ha trivial

theorem level_smul (q : LevQ Dw l) : (l.M : 𝓞 E) • q = 0 := by
  have h : Ideal.span {((l.M : ℕ) : 𝓞 E)} ≤ l.Mb := l.prod.symm.le.trans Ideal.mul_le_left
  exact quot_smul (h (Ideal.mem_span_singleton_self _)) q

theorem fixesDatum_of_congAt (c : Coeff l) {n b : ℕ} (hb : l.M ∣ b) {g : Matrix (Fin n) (Fin n) E}
    (h : UnRep.CongAt (stdLat E n) b b g) (w : (Fin n → LevQ Dw l) → c.F) : FixesDatum c g w := by
  obtain ⟨t, ht, u, hu⟩ := entries_of_congAt h
  rintro q q' ⟨k, G, hk, hG, hq⟩
  congr 1
  funext i
  obtain ⟨e, rfl⟩ := hb
  have hent : ∀ j, (t : 𝓞 E) * G i j =
      (if i = j then (t : 𝓞 E) * k else 0) + (k * e * u i j) * (l.M : 𝓞 E) := fun j => by
    apply RingOfIntegers.coe_injective
    have h1 := hu i j
    have h2 := hG i j
    simp only [RingOfIntegers.coe_eq_algebraMap] at h1 h2
    simp only [map_mul, map_add (f := _), map_natCast, h2, apply_ite (algebraMap (𝓞 E) E), map_zero]
    push_cast at h1
    split_ifs at h1 ⊢ <;> linear_combination (k : E) * h1
  have key : ((t : 𝓞 E) * k) • (q' i - q i) = 0 := by
    rw [smul_sub, mul_smul, hq i, Finset.smul_sum]
    simp only [smul_smul, hent, add_smul, mul_smul _ (l.M : 𝓞 E), level_smul, smul_zero, add_zero, ite_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
  have hco : IsCoprime ((t * k : ℕ) : 𝓞 E) (l.M : 𝓞 E) :=
    (ht.coprime_mul_right_right.mul_left hk).cast
  obtain ⟨x, y, hxy⟩ := hco
  rw [← sub_eq_zero, ← one_smul (𝓞 E) (q' i - q i), ← hxy, add_smul, mul_smul, mul_smul y, level_smul,
    Nat.cast_mul, key, smul_zero, smul_zero, add_zero]

theorem evR_mul (Xo : Moduli Dw l) (c : Coeff l) (z : c.F) (f f' : Rul Xo c)
    (hf : ∀ p y, f' p y = algebraMap c.F p.R z * f p y) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    evR Xo c f' y = algebraMap c.F S z * evR Xo c f y := by
  unfold evR evalAt
  split_ifs
  · rw [hf, map_mul, AlgHom.commutes]
  · rw [mul_zero]

section Cover

variable {Xo : Moduli Dw l} {c : Coeff l} {n : ℕ} (d : DeltaDat Xo c n)

theorem isBeta_cover (hK : KPsiIn (Dw := Dw) c) {bad : ℕ} (hb : bad ≠ 1) (Λ : GenLat E n) (hU : Λ.Unimod)
    (hT : Λ.TrivAt bad) : IsBeta Dw d.c₂ Λ (d.eF (betaH (Dw := Dw) c Λ)) := by
  have hex := GlobalTheory.betaExists_of_ne_one E H Dw l c n bad hb hK Λ hU hT
  have hs := hex.choose_spec
  have e : betaH (Dw := Dw) c Λ = hex.choose := dif_pos hex
  rw [e]
  refine ⟨by simpa using hs.1, (PlaceInt.eF_transfer E H Dw l Xo c n d Λ).1 _ hs.2.1, fun s => ?_⟩
  exact hs.2.2 (s.comp (d.eF : c.F →+* d.c₂.F))

theorem map_pushLet (g : Matrix (Fin n) (Fin n) E) (P : MvPolynomial (LtN Dw n) c.F) :
    MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (pushLet c g P) =
      pushLet d.c₂ g (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
  have he : ∀ τ x, (d.eF : c.F →+* d.c₂.F) (embF c τ x) = embF d.c₂ τ x := PlaceInt.eF_embF d
  generalize (d.eF : c.F →+* d.c₂.F) = f at he ⊢
  induction P using MvPolynomial.induction_on with
  | C a => simp [pushLet]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, MvPolynomial.map_X]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [pushLet, MvPolynomial.aeval_X, letB, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, he]

end Cover

end GlobalTheory.ShortMove
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.ShortChange

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem trivAt_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {Λ : GenLat E n} {a b : ℕ}
    (ha : Λ.TrivAt a) (hb : Λ.TrivAt b) : Λ.TrivAt (a * b) := by
  obtain ⟨k, hk, h1, h2⟩ := ha
  obtain ⟨m, hm, h3, h4⟩ := hb
  have hg : Ideal.span {((Nat.gcd k m : ℕ) : 𝓞 E)} ≤ Ideal.span {(k : 𝓞 E)} ⊔ Ideal.span {(m : 𝓞 E)} := by
    rw [Ideal.span_singleton_le_iff_mem]
    have e : ((Nat.gcd k m : ℕ) : 𝓞 E) = (k : 𝓞 E) * (Nat.gcdA k m : ℤ) + (m : 𝓞 E) * (Nat.gcdB k m : ℤ) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) (Nat.gcd_eq_gcd_ab k m)
      push_cast at this
      exact this
    rw [e]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  refine ⟨Nat.gcd k m, (hk.coprime_dvd_left (Nat.gcd_dvd_left _ _)).mul_right
    (hm.coprime_dvd_left (Nat.gcd_dvd_right _ _)), ?_, ?_⟩
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h1 h3
  · refine (Submodule.smul_mono hg le_rfl).trans ?_
    rw [Submodule.sup_smul]
    exact sup_le h2 h4

theorem badOK_host (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) :
    BadOK l (D.host.QS * D.host.q * D.host.d * l.M) := by
  have hqd := D.host.qd_big
  have hM := l.three_le
  refine ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega)) (by omega),
    D.host.toHostRaw.two_dvd_condN.mul_right _, Dvd.intro_left _ rfl, fun p hp h => ?_⟩
  exact dvd_mul_of_dvd_left (D.host.der.discr_primes.1 p hp h) _

theorem odd_rank {D : D7} (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) :
    Odd ((T.Q.Dw j).p + (T.Q.Dw j).q) := by
  obtain ⟨h1, h2, -⟩ := hF.p.toLawsCore.pins.2.2.2 j hj
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  obtain ⟨hj1, hj2⟩ := hj
  rw [h1, h2]
  exact ⟨a + b - 1, by unfold Ranks.sigW; dsimp only; omega⟩

end GlobalTheory.ShortChange
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAdaptedCongr
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct Matrix

namespace GlobalTheory.AdaptCongr

open GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.Move

theorem exists_move_split : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (n M bad : ℕ) (Λ : GenLat E n), 0 < M → 0 < bad → Λ.Unimod → Λ.TrivAt M → ∃ (γ : GL (Fin n) E) (Λ' : GenLat E n), IsUnE (IsCMField.complexConj E) 1 γ.1 ∧ CongAt (stdLat E n) M M γ.1 ∧ (∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La) ∧ Λ'.Unimod ∧ ∃ s : 𝓞 E, s ≠ 0 ∧ Ideal.span {s} • Λ'.La ≤ stdLat E n ∧ Ideal.span {s} • stdLat E n ≤ Λ'.La ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P ∧ ((bad * M : ℕ) : 𝓞 E) ∉ P) ∧ ∃ k : ℕ, k.Coprime (bad * M) ∧ Ideal.span {(k : 𝓞 E)} • Λ'.La ≤ stdLat E n ∧ Ideal.span {(k : 𝓞 E)} • stdLat E n ≤ Λ'.La := by
  intro E _ _ _ H n M bad Λ hM hbad hU hT
  obtain ⟨hherm, hrk, hfg, hsp, -, -, hmov, hun⟩ := GlobalTheory.T.standardHermitianForm_hostField_inhabitant E H n
  obtain ⟨g, hg, hΛ, hgc⟩ := GlobalTheory.T.exists_adelic_unitary_translate_standardLattice E H n M Λ hM hU hT
  obtain ⟨γ, hγ, ⟨t₁, ht₁, hc₁⟩, s, ⟨hs0, hs⟩, hint⟩ := GlobalTheory.T.exists_rational_unitary_split_denominator (maximalRealSubfield E) E
    (IsCMField.complexConj E) n 1 hherm hrk (stdLat E n) hfg hsp g (bad * M) hg (Nat.mul_pos hbad hM)
  obtain ⟨t₂, ht₂, hc₂⟩ := hgc M hM
  have hrat := (hat_rational_points_and_approx (maximalRealSubfield E) E n (stdLat E n) hfg hsp).1
  have hmem : ∀ v, v ∈ Λ.La ↔ ∃ z ∈ hat (maximalRealSubfield E) (stdLat E n : Set (Fin n → E)),
      g.1 *ᵥ z = fv (maximalRealSubfield E) v := by
    intro v
    rw [← SetLike.mem_coe, hΛ]
    rfl
  have hinv : ∀ v : Fin n → E, (γ⁻¹).1 *ᵥ (γ.1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hinv' : ∀ v : Fin n → E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  let Λ' : GenLat E n := ⟨Λ.La.comap ((Matrix.mulVecLin (γ⁻¹).1).restrictScalars (𝓞 E))⟩
  have hΛ' : ∀ v, v ∈ Λ'.La ↔ (γ⁻¹).1 *ᵥ v ∈ Λ.La := fun v => Iff.rfl
  have hmove : ∀ v, v ∈ Λ.La ↔ γ.1 *ᵥ v ∈ Λ'.La := fun v => by rw [hΛ', hinv]
  have hsE : ∀ v : Fin n → E, s • v = (s : E) • v := fun v => rfl
  have h1 : ∀ v ∈ Λ'.La, s • v ∈ stdLat E n := by
    intro v hv
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 ((hΛ' v).1 hv)
    have := (hint z hz).1
    rw [← Matrix.mulVec_mulVec, hzv, ← fv_mulVec, hinv', ← fv_smul] at this
    rw [hsE]
    exact (hrat _).1 this
  have h2 : ∀ v ∈ stdLat E n, s • v ∈ Λ'.La := by
    intro v hv
    have := (hint _ ((hrat v).2 hv)).2
    rw [hΛ', hmem]
    refine ⟨_, this, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← fv_mulVec, ← fv_smul, hsE, Matrix.mulVec_smul]
  obtain ⟨k, hk, hsk⟩ := exists_nat_coprime s (bad * M) fun P hP hsP => (hs P hP hsP).2
  refine ⟨γ, Λ', hγ, ?_, hmove, unimod_move γ hγ Λ Λ' hmove hU, s, hs0, (span_smul_le _ _ _).2 h1,
    (span_smul_le _ _ _).2 h2, fun P hP hsP => ⟨(hmov P hP).1 (hs P hP hsP).1, (hs P hP hsP).2⟩, k, hk,
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h1 v hv),
    (span_smul_le _ _ _).2 fun v hv => smul_mem_of_dvd hsk (h2 v hv)⟩
  · obtain ⟨j, hj, -, hj2⟩ := hT
    refine ⟨t₁ * t₂ * j, (ht₁.coprime_mul_left_right.mul_left ht₂).mul_left hj, fun v hv => ?_⟩
    have hjv : j • v ∈ Λ.La := by
      have := (span_smul_le _ _ _).1 hj2 v hv
      rwa [Nat.cast_smul_eq_nsmul] at this
    obtain ⟨z, hz, hzv⟩ := (hmem _).1 hjv
    obtain ⟨w₁, hw₁, e₁⟩ := hc₁ z hz
    obtain ⟨w₂, hw₂, e₂⟩ := hc₂ z hz
    have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (t₁ * t₂ * j) • (γ.1 *ᵥ v - v) = M • ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v))) := by
      rw [← Nat.cast_smul_eq_nsmul E M, smul_smul, mul_inv_cancel₀ hME, one_smul]
    refine ⟨_, ?_, key⟩
    rw [← hrat]
    have e : fv (maximalRealSubfield E) ((M : E)⁻¹ • ((t₁ * t₂ * j) • (γ.1 *ᵥ v - v)))
        = (t₂ * bad) • w₁ - t₁ • w₂ := by
      refine nsmul_cancel _ hM ?_
      rw [← cap_fv_nsmul, ← key, mul_smul, smul_sub j, ← Matrix.mulVec_smul, cap_fv_nsmul, fv_sub, fv_mulVec,
        ← hzv, Matrix.mulVec_mulVec]
      have a1 : M • ((t₂ * bad) • w₁) = t₂ • ((bad * M) • w₁) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      have a2 : M • (t₁ • w₂) = t₁ • (M • w₂) := smul_comm _ _ _
      rw [smul_sub M, a1, a2, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm t₂ t₁, ← smul_sub, sub_sub_sub_cancel_right]
    rw [e]
    exact sub_mem (nsmul_mem hw₁ _) (nsmul_mem hw₂ _)

end GlobalTheory.AdaptCongr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortRuleChangeMat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem shortRule_change_mat (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ)
    (Λ : GenLat D.host.E n) (g : Matrix (Fin n) (Fin n) D.host.E) (b : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hg : IsUnitaryM g) (hb : (T.dδ j n).l₂.M ∣ b)
    (hcg : GlobalTheory.UnRep.CongAt (stdLat D.host.E n) b b g)
    (hev : Even n) (hU : Λ.Unimod) (hU' : (actLat g Λ).Unimod) (hT : Λ.TrivAt (badN D))
    (hT' : (actLat g Λ).TrivAt (badN D)) (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hM' : (actLat g Λ).TrivAt (T.dδ j n).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (P' : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F), P' ∈ harmL T.Q.c (actLat g Λ) a ∧ ζ ≠ 0 ∧
      (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin n → (T.Q.Dw j).La) (N N' : ℕ) (f : Rul (T.Q.Xo j) T.Q.c),
        Λ.LevOK N (T.dδ j n).l₂.M → (actLat g Λ).LevOK N' (T.dδ j n).l₂.M →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) (actLat g Λ) N' x0 P' (ζ • f) := by
  set d := T.dδ j n with hd
  obtain ⟨_, hnab⟩ := hF.sh.dNab j hj n
  have hCI := GlobalTheory.T.harmonic_germ_value_chart_independent
  have hbad := GlobalTheory.ShortChange.badOK_host D T.Q.H d.l₂
  have hdv : D.host.QS * D.host.q * D.host.d ∣ badN D := Dvd.intro _ rfl
  have hb1 : D.host.QS * D.host.q * D.host.d * d.l₂.M ≠ 1 := fun h => by
    have := hbad.2.1
    omega
  have hB := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT) hM
  have hB' := GlobalTheory.ShortChange.trivAt_mul (trivAt_of_dvd hdv hT') hM'
  have hK := hF.p.kPsi j hj
  obtain ⟨ze, ⟨k, hk, hze⟩, hrep⟩ := GlobalTheory.T.thetaChangeOfRepRootOfUnity_of_chartIndependence hCI D.host.E T.Q.H (T.Q.Dw j) d.l₂ d.Xo₂ d.c₂ d.nab₂ n
    ⟨(GlobalTheory.PlaceInt.host_galois_discr_moves D T.Q.H).1, GlobalTheory.ShortChange.odd_rank T hF j hj, hev, hnab⟩ _ hbad
    Λ g _ _ hU hg hB hB' (isBeta_cover d hK hb1 Λ hU hB) (isBeta_cover d hK hb1 _ hU' hB')
  have hP' := ((GlobalTheory.PushKeeps.push_keeps D.host.E T.Q.H (T.Q.Dw j) T.Q.l T.Q.c n a g hg).2 Λ).2.2.2 P hP
  have hz : d.eF.symm ze ^ k = 1 := by rw [← map_pow, hze, map_one]
  refine ⟨pushLet T.Q.c g P, d.eF.symm ze, hP', fun h0 => ?_, ⟨k, hk, hz⟩,
    fun x0 N N' f hN hN' hR K _ _ _ _ hKe y y₂ hy => ?_⟩
  · rw [h0, zero_pow hk.ne'] at hz
    exact zero_ne_one hz
  obtain ⟨v, hv, hval⟩ := hR K hKe y y₂ hy
  have h₂ := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d Λ).2.1 a P hP).1)
  have h₂' := (((GlobalTheory.PlaceInt.eF_transfer D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n d _).2.1 a _ hP').1)
  obtain ⟨v', hv', -⟩ := (GlobalTheory.shortThetaValue_existsUnique_natural GlobalTheory.firstFiveLaws.1 hCI D.host.E T.Q.H (T.Q.Dw j)
    d.l₂ d.Xo₂ d.c₂ d.nab₂ hnab n _ N' hU' hM' hN' a _ h₂'.1 (d.w x0)
    (d.eF (betaH (Dw := T.Q.Dw j) T.Q.c (actLat g Λ)))).1 K y₂
  refine ⟨v', hv', ?_⟩
  rw [map_pushLet] at hv'
  have hvv := hrep (d.w x0) (fixesDatum_of_congAt d.c₂ hb hcg _) N N' hN hN' a _ h₂ K y₂ v v' hv hv'
  have hs : evR (T.Q.Xo j) T.Q.c (d.eF.symm ze • f) y =
      algebraMap T.Q.c.F K (d.eF.symm ze) * evR (T.Q.Xo j) T.Q.c f y :=
    evR_mul (T.Q.Xo j) T.Q.c _ f _ (fun p y => Algebra.smul_def _ _) y
  rw [hs, hval, hvv, ← hKe, AlgEquiv.apply_symm_apply]
  ring

theorem congAt_of_cols {E : Type} [Field E] [NumberField E] {n : ℕ} (gm : Matrix (Fin n) (Fin n) E) (m : ℕ)
    (h : ∀ j : Fin n, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence.CongAt m (fun i => gm i j)
      fun i => (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) :
    GlobalTheory.UnRep.CongAt (stdLat E n) m m gm := by
  choose k hk b hb using h
  refine ⟨∏ j, k j, Nat.Coprime.prod_left fun j _ => hk j, fun v hv => ?_⟩
  have hv' : ∀ i, ∃ y : 𝓞 E, (y : E) = v i := fun i => by
    have := (Submodule.mem_pi.1 hv) i (Set.mem_univ _)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  choose y hy using hv'
  refine ⟨fun i => ((∑ j, ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : 𝓞 E) * b j i * y j : 𝓞 E) : E), ?_, ?_⟩
  · refine Submodule.mem_pi.2 fun i _ => Submodule.mem_one.2 ⟨_, rfl⟩
  · funext i
    have e1 : ∀ j, ((∏ l, k l : ℕ) : E) * (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) =
        ((∏ l ∈ Finset.univ.erase j, k l : ℕ) : E) * ((m : E) * (b j i : E)) := fun j => by
      have hp : (∏ l, k l) = k j * ∏ l ∈ Finset.univ.erase j, k l :=
        (Finset.mul_prod_erase (s := Finset.univ) (f := k) (Finset.mem_univ j)).symm
      rw [hp]
      push_cast
      have h' := hb j i
      simp only at h'
      linear_combination (∏ l ∈ Finset.univ.erase j, ((k l : ℕ) : E)) * h'
    have e2 : (gm.mulVec v - v) i = ∑ j, (gm i j - (((1 : Matrix (Fin n) (Fin n) (𝓞 E)) i j : 𝓞 E) : E)) * v j := by
      simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib]
      congr 1
      simp [Matrix.one_apply]
    simp only [Pi.smul_apply, nsmul_eq_mul, e2]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hy j]
    have h' := e1 j
    push_cast at h'
    linear_combination ((y j : 𝓞 E) : E) * h'

theorem plc_prime {K : Type} [Field K] [NumberField K] (lam : HeightOneSpectrum (𝓞 K)) : (Formalism.EigenvalueLevelCeiling.plc lam).Prime := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  haveI : lam.asIdeal.IsPrime := lam.isPrime
  have hne : Ideal.absNorm lam.asIdeal ≠ 0 := fun h => lam.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hz : ((Ideal.absNorm lam.asIdeal : ℕ) : 𝓞 K ⧸ lam.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk lam.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.absNorm_mem _
  have hd : ringChar (𝓞 K ⧸ lam.asIdeal) ∣ Ideal.absNorm lam.asIdeal :=
    (ringChar.spec (𝓞 K ⧸ lam.asIdeal) _).1 hz
  rcases CharP.char_is_prime_or_zero (𝓞 K ⧸ lam.asIdeal) (ringChar (𝓞 K ⧸ lam.asIdeal)) with h | h
  · exact h
  · rw [h, zero_dvd_iff] at hd
    exact absurd hd hne



attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem star_mem_one (D : D7) {x : D.host.E} (hx : x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    star x ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨star (algebraMap _ _ y),
    (RingOfIntegers.isIntegral_coe y).map (starRingEnd D.host.E).toIntAlgHom⟩, rfl⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem zero_case (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (hL : Formalism.IndefR.Bridge.hLat V 1 = stdLat D.host.E V.rank)
    (Λ : GenLat D.host.E V.rank) (hT : Λ.TrivAt 0) :
    (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V 1)) ∧
      (∀ b, Formalism.IndefR.FWT.SplitOffBad V b 1) ∧ ∀ m, Λ.TrivAt m := by
  obtain ⟨k, hk, h1, h2⟩ := hT
  obtain rfl : k = 1 := (Nat.coprime_zero_right k).1 hk
  simp only [Nat.cast_one, Ideal.span_singleton_one, Submodule.top_smul] at h1 h2
  have hΛ : Λ.La = stdLat D.host.E V.rank := le_antisymm h1 h2
  refine ⟨fun w => ?_, fun b => ?_, fun m => ⟨1, Nat.coprime_one_left m, by simpa using h1, by simpa using h2⟩⟩
  · have hf : Formalism.IndefR.FWT.fin V (1 : Formalism.L2.Theta.GA D V) = 1 := map_one _
    rw [hf, hL, hΛ]
    constructor
    · intro hw
      exact Submodule.mem_pi.2 fun i _ => star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
    · intro hw
      refine Submodule.mem_pi.2 fun i _ => ?_
      have := star_mem_one D ((Submodule.mem_pi.1 hw) i (Set.mem_univ _))
      simpa only [star_star] using this
  · refine ⟨one_mem _, 0, ∅, ⟨⟨fun _ => 0, by simp, by simp⟩, by simp⟩, by simp, fun a c => ?_⟩
    have : Formalism.L2.Theta.mt V (1 : Formalism.L2.Theta.GA D V) = 1 := by simp [Formalism.L2.Theta.mt]
    simp [this]

end GlobalTheory.OrbitAdapt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupport
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.OrbitAdapt

section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out Formalism.MainNotions.WeightAlgebra GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove

theorem exists_step_int (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (n : ℕ) (hev : Even n)
    (hb : 0 < badN D) (Λ : GenLat D.host.E n) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (hU : Λ.Unimod) (hT : Λ.TrivAt (badN D))
    (hM : Λ.TrivAt (T.dδ j n).l₂.M) (hN : Λ.LevOK N (T.dδ j n).l₂.M) (hP : P ∈ harmL T.Q.c Λ a) (p : ℕ)
    (hp : 0 < p) :
    ∃ (Λ₁ : GenLat D.host.E n) (N₁ : ℕ) (P₁ : MvPolynomial (LtN (T.Q.Dw j) n) T.Q.c.F) (ζ : T.Q.c.F),
      Λ₁.Unimod ∧ Λ₁.TrivAt (badN D * (T.dδ j n).l₂.M * p) ∧ Λ₁.LevOK N₁ (T.dδ j n).l₂.M ∧ P₁ ∈ harmL T.Q.c Λ₁ a ∧
      ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      (∀ (x0 : Fin n → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j n) Λ₁ N₁ x0 P₁ (ζ • f)) := by
  have hBM := GlobalTheory.ShortChange.trivAt_mul hT hM
  have hMpos : 0 < (T.dδ j n).l₂.M := by have := (T.dδ j n).l₂.three_le; omega
  obtain ⟨γ, Λ', hγ, hc, hmove, hU', s, -, -, -, -, k, hk, hk1, hk2⟩ :=
    GlobalTheory.AdaptCongr.exists_move_split D.host.E T.Q.H n _ p Λ (Nat.mul_pos hb hMpos) hp hU hBM
  have h2b : 2 ∣ badN D := by
    unfold badN
    exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
  have hg : IsUnitaryM γ.1 := by
    refine Matrix.ext fun i l => ?_
    have := hγ (Pi.single l 1) (Pi.single i 1)
    rw [GlobalTheory.UnRep.Move.hermE_one, GlobalTheory.UnRep.Move.hermE_one] at this
    simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
    simp only [adjM, Matrix.mul_apply, Matrix.of_apply, this, Matrix.one_apply, Pi.single_apply]
    by_cases h : i = l
    · subst h; simp [apply_ite (IsCMField.complexConj D.host.E)]
    · simp [h, apply_ite (IsCMField.complexConj D.host.E), Ne.symm h]
  have hinv' : ∀ v : Fin n → D.host.E, γ.1 *ᵥ ((γ⁻¹).1 *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  obtain rfl : Λ' = actLat γ.1 Λ := by
    cases Λ' with
    | mk L =>
      simp only [actLat, GenLat.mk.injEq]
      ext v
      constructor
      · intro hv
        exact ⟨_, (hmove _).2 (by rw [hinv']; exact hv), hinv' v⟩
      · rintro ⟨u, hu, rfl⟩
        exact (hmove u).1 hu
  have hkT : ∀ m, m ∣ p * (badN D * (T.dδ j n).l₂.M) → (actLat γ.1 Λ).TrivAt m := fun m hm =>
    ⟨k, hk.coprime_dvd_right hm, hk1, hk2⟩
  have hN₁ : (actLat γ.1 Λ).LevOK ((T.dδ j n).l₂.M * k) (T.dδ j n).l₂.M := by
    refine ⟨?_, dvd_mul_right _ _, ?_⟩
    · exact (T.dδ j n).l₂.odd.mul
        (Nat.coprime_two_right.1 (hk.coprime_dvd_right ((h2b.mul_right _).mul_left _)))
    · show _ ≤ (actLat γ.1 Λ).La ⊓ Formalism.L2.Pj.stdLat D.host.E n
      refine le_inf ((Submodule.smul_mono_left ?_).trans hk2) Submodule.smul_le_right
      refine Ideal.span_singleton_le_span_singleton.2 ?_
      rw [Nat.cast_mul]
      exact dvd_mul_left _ _
  obtain ⟨P₁, ζ, hP₁, hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj n Λ γ.1 _ a P hg
    (dvd_mul_left _ _) hc hev hU hU' hT (hkT _ ((dvd_mul_right _ _).mul_left _)) hM
    (hkT _ ((dvd_mul_left _ _).mul_left _)) hP
  exact ⟨actLat γ.1 Λ, _, P₁, ζ, hU', hkT _ (by rw [mul_comm]), hN₁, hP₁, hζ, hroot,
    fun x0 f h => hR x0 N _ f hN hN₁ h⟩

theorem exists_step_split_off (D : D7) (T : Full D) (hF : LawsFull T) (j : ℕ) (hj : InR D j) (V : Formalism.BasicNotions.TH.HSp D)
    (hg : V.gram = 1) (hL : Formalism.IndefR.Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank) (hev : Even V.rank) (hb : 0 < badN D)
    (p : ℕ) (hp : 0 < p) (Λ : GenLat D.host.E V.rank) (N : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (hU : Λ.Unimod)
    (hT : Λ.TrivAt (badN D * (T.dδ j V.rank).l₂.M * p)) (hN : Λ.LevOK N (T.dδ j V.rank).l₂.M)
    (hP : P ∈ harmL T.Q.c Λ a) :
    ∃ (h : Formalism.L2.Theta.GA D V) (Λ' : GenLat D.host.E V.rank) (N' : ℕ)
      (P' : MvPolynomial (LtN (T.Q.Dw j) V.rank) T.Q.c.F) (ζ : T.Q.c.F),
      Formalism.IndefR.FWT.SplitOffBad V (badN D * (T.dδ j V.rank).l₂.M * p) h ∧
      (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Formalism.IndefR.Bridge.hLat V (Formalism.IndefR.FWT.fin V h)) ∧
      Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ j V.rank).l₂.M ∧ Λ'.TrivAt p ∧
      Λ'.LevOK N' (T.dδ j V.rank).l₂.M ∧ P' ∈ harmL T.Q.c Λ' a ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
      ∀ (x0 : Fin V.rank → (T.Q.Dw j).La) (f : Rul (T.Q.Xo j) T.Q.c),
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ N x0 P f →
        IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j V.rank) Λ' N' x0 P' (ζ • f) := by
  have hM0 : 0 < (T.dδ j V.rank).l₂.M := by have := (T.dδ j V.rank).l₂.three_le; omega
  have hpos : 0 < badN D * p * (T.dδ j V.rank).l₂.M := Nat.mul_pos (Nat.mul_pos hb hp) hM0
  have hT' : Λ.TrivAt (badN D * p * (T.dδ j V.rank).l₂.M) := by
    rwa [show badN D * p * (T.dδ j V.rank).l₂.M = badN D * (T.dδ j V.rank).l₂.M * p by ring]
  obtain ⟨gm, h, hgm, hc, hh, hs, e⟩ := GlobalTheory.T.exists_rationalUnitary_move_selfDual_to_split D V hg hL T.Q.H _ hpos Λ hU hT'
  have h2 : 2 ∣ badN D * p := by
    unfold badN
    exact dvd_mul_of_dvd_left (((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _) p
  obtain ⟨N', c1, c2, c3, c4, -⟩ := GlobalTheory.SplitReps.exists_conjLat V hg hL T.Q.H (T.dδ j V.rank).l₂ (badN D * p) h2 h hs
  rw [← e] at c1 c2 c3 c4
  have hcg := congAt_of_cols gm _ hc
  have hTb : Λ.TrivAt (badN D) := trivAt_of_dvd ⟨(T.dδ j V.rank).l₂.M * p, by ring⟩ hT
  have hTM : Λ.TrivAt (T.dδ j V.rank).l₂.M := trivAt_of_dvd ⟨badN D * p, by ring⟩ hT
  obtain ⟨P', ζ, hP', hζ, hroot, hR⟩ := shortRule_change_mat D T hF j hj V.rank Λ gm _ a P hgm
    (dvd_mul_left _ _) hcg hev hU c1 hTb (trivAt_of_dvd (dvd_mul_right _ _) c2) hTM c3 hP
  have hsp : Formalism.IndefR.FWT.SplitOffBad V (badN D * p * (T.dδ j V.rank).l₂.M) h :=
    GlobalTheory.SplitReps.splitOffBad_of_suppSplit V _ h hh hs
  refine ⟨h, actLat gm Λ, N', P', ζ, ?_, fun w => by rw [e]; rfl, c1, trivAt_of_dvd (dvd_mul_right _ _) c2, c3,
    trivAt_of_dvd (dvd_mul_left _ _) c2, c4, hP', hζ, hroot, fun x0 f hf => hR x0 N N' f hN c4 hf⟩
  rwa [show badN D * (T.dδ j V.rank).l₂.M * p = badN D * p * (T.dδ j V.rank).l₂.M by ring]

theorem splitOffBad_of_dvd (D : D7) (V : Formalism.BasicNotions.TH.HSp D) {a b : ℕ} (hab : a ∣ b) {h : Formalism.L2.Theta.GA D V}
    (hs : Formalism.IndefR.FWT.SplitOffBad V b h) : Formalism.IndefR.FWT.SplitOffBad V a h := by
  obtain ⟨h1, e', Q, h3, h4, h5⟩ := hs
  obtain ⟨c, rfl⟩ := hab
  refine ⟨h1, e', Q, h3, fun PP hP hbd => h4 PP hP ?_, h5⟩
  rw [Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ hbd

end


open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence GlobalTheory.ShortMove in
set_option maxHeartbeats 1000000 in
theorem exists_adapted : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ fw O hT hk i hO ℓ U lam f hf
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hrk : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have hn : (κ i).n = (Vc D i).rank := (fw.kap i (D.eTau.symm 1)).2.2.trans hrk.symm
  have hr : Odd D.R.r := by
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have hev : Even (Vc D i).rank := hrk ▸ hr.add_odd D.R.t_odd
  have hV := hO.2.lift.std
  have hg : (Vc D i).gram = 1 := hV.1
  have hL : Bridge.hLat (Vc D i) 1 = Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank := hV.2
  rw [hn] at hf
  obtain ⟨Λ, N, x₀, P, x, hU, hTb, hTM, hN, hA, hP, hx⟩ := hf
  have hp := plc_prime lam
  have hq : 0 < Formalism.EigenvalueLevelCeiling.plc lam * (O i).bad () := Nat.mul_pos hp.pos (hO.2.bad ()).1
  obtain ⟨h, Λ', N', P', ζ, hs, hmem, hU', hTb', hTM', hTp, hN', hP', hζ, ⟨m, hm, hζm⟩, hR⟩ :
      ∃ (h : GA D (Vc D i)) (Λ' : GenLat D.host.E (Vc D i).rank) (N' : ℕ)
        (P' : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (ζ : T.Q.c.F),
        SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧
        (∀ w, w ∈ Λ'.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧
        Λ'.Unimod ∧ Λ'.TrivAt (badN D) ∧ Λ'.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        Λ'.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ'.LevOK N' (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧
        P' ∈ harmL T.Q.c Λ' (wtA (κ i)) ∧ ζ ≠ 0 ∧ (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧
        ∀ (x0 : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (g : Rul (T.Q.Xo ((i : ℕ) + 1)) T.Q.c),
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N x0 P g →
          IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ' N' x0 P' (ζ • g) := by
    rcases Nat.eq_zero_or_pos (badN D) with hb | hb
    · rw [hb] at hTb
      obtain ⟨h1, h2, h3⟩ := zero_case D (Vc D i) hL Λ hTb
      exact ⟨1, Λ, N, P, 1, h2 _, h1, hU, h3 _, h3 _, h3 _, hN, hP, one_ne_zero, ⟨1, one_pos, one_pow _⟩,
        fun x0 g hg => by rwa [one_smul]⟩
    · obtain ⟨Λ₁, N₁, P₁, ζ₁, hU₁, hT₁, hN₁, hP₁, hζ₁, ⟨m₁, hm₁, e₁⟩, hR₁⟩ :=
        exists_step_int D T hT ((i : ℕ) + 1) hj _ hev hb Λ N (wtA (κ i)) P hU hTb hTM hN hP _ hq
      obtain ⟨h, Λ', N', P', ζ₂, d1, d2, d3, d4, d5, d6, d7, d8, hζ₂, ⟨m₂, hm₂, e₂⟩, hR₂⟩ :=
        exists_step_split_off D T hT _ hj (Vc D i) hg hL hev hb _ hq Λ₁ N₁ _ P₁ hU₁ hT₁ hN₁ hP₁
      refine ⟨h, Λ', N', P', ζ₂ * ζ₁, splitOffBad_of_dvd D _ ⟨Formalism.EigenvalueLevelCeiling.plc lam, by ring⟩ d1, d2, d3, d4, d5,
        trivAt_of_dvd (dvd_mul_right _ _) d6, d7, d8, mul_ne_zero hζ₂ hζ₁,
        ⟨m₁ * m₂, Nat.mul_pos hm₁ hm₂, by rw [mul_pow, pow_mul' ζ₂, e₂, pow_mul ζ₁, e₁, one_pow, one_pow, one_mul]⟩,
        fun x0 g hg => ?_⟩
      rw [mul_smul]
      exact hR₂ x0 _ (hR₁ x0 g hg)
  have hint : IsIntegral ℤ (ζ ^ (m - 1)) :=
    IsIntegral.pow (IsIntegral.of_pow hm (by rw [hζm]; exact isIntegral_one)) _
  have hinv : ζ ^ (m - 1) * ζ = 1 := by rw [← pow_succ, Nat.sub_add_cancel hm, hζm]
  refine ⟨⟨ζ ^ (m - 1), hint⟩, 1, fun u => ⟨ζ • (f u).1, Submodule.smul_mem _ ζ (f u).2⟩, Λ', h, N', x₀, P', x,
    ?_, fun u => ?_, hs, hmem, hTp, hU', hTb', hTM', hN', hA, hP', fun u => ⟨(hx u).1, (hx u).2.1, hR _ _ (hx u).2.2⟩⟩
  · rw [Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 lam.isPrime.ne_top
  · show ((1 : ℕ) : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (ζ ^ (m - 1)) • (ζ • ((f u).1 : T.R ((i : ℕ) + 1)))
    rw [Nat.cast_one, one_smul, smul_smul, hinv, one_smul]

end GlobalTheory.OrbitAdapt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrbitFamilyAdaptedLatticeSplitSupportStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orbit_family_adapted_lattice_split_support : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)) (U : Subgroup G) (lam : HeightOneSpectrum (𝓞 D.what₂.LL)) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)), IsOrbitFamily (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (badN D) (wtA (κ i)) (T.dδ ((i : ℕ) + 1) (κ i).n) (fun u : U => ℓ u) (fun u => ((f u).1 : T.R ((i : ℕ) + 1))) → ∃ (a : 𝓞 T.Q.c.F) (s : ℕ) (f' : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)) (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La), (s : 𝓞 D.what₂.LL) ∉ lam.asIdeal ∧ (∀ u, (s : T.Q.c.F) • ((f u).1 : T.R ((i : ℕ) + 1)) = (a : T.Q.c.F) • ((f' u).1 : T.R ((i : ℕ) + 1))) ∧ SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M * (O i).bad ()) h ∧ (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) ∧ Λ.TrivAt (Formalism.EigenvalueLevelCeiling.plc lam) ∧ Λ.Unimod ∧ Λ.TrivAt (badN D) ∧ Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M ∧ AdmX (l := T.Q.l) true x₀ ∧ P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) ∧ ∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f' u).1 : T.R ((i : ℕ) + 1)) := by
  first | exact @GlobalTheory.OrbitAdapt.exists_adapted | exact GlobalTheory.OrbitAdapt.exists_adapted | (intros; apply GlobalTheory.OrbitAdapt.exists_adapted <;> assumption)
end
