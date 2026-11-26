module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExpNegOneLtOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.ThetaMove

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

def Dom (S : Finset (HeightOneSpectrum (𝓞 E))) (M₁ M₂ : Submodule (𝓞 E) W) : Prop :=
  (∀ P ∈ S, localization₂ P.asIdeal M₂ ≤ localization₂ P.asIdeal M₁) ∧ ∀ Q, Q ∉ S → localization₂ Q.asIdeal M₁ ≤ localization₂ Q.asIdeal M₂

def Full (M : Submodule (𝓞 E) W) : Prop := ∀ x : W, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • x ∈ M

theorem Dom.refl (S : Finset (HeightOneSpectrum (𝓞 E))) (M : Submodule (𝓞 E) W) : Dom S M M :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩

theorem Dom.trans {S : Finset (HeightOneSpectrum (𝓞 E))} {M₁ M₂ M₃ : Submodule (𝓞 E) W} (h : Dom S M₁ M₂) (h' : Dom S M₂ M₃) :
    Dom S M₁ M₃ :=
  ⟨fun P hP => (h'.1 P hP).trans (h.1 P hP), fun Q hQ => (h.2 Q hQ).trans (h'.2 Q hQ)⟩

theorem Full.inf {M M' : Submodule (𝓞 E) W} (h : Full M) (h' : Full M') : Full (M ⊓ M') := by
  intro x
  obtain ⟨n, hn, hx⟩ := h x
  obtain ⟨m, hm, hy⟩ := h' x
  refine ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
  · rw [Nat.cast_mul, mul_smul]; exact M'.smul_mem _ hy

theorem localization_mono (Q : HeightOneSpectrum (𝓞 E)) {M M' : Submodule (𝓞 E) W} (h : M ≤ M') :
    localization₂ Q.asIdeal M ≤ localization₂ Q.asIdeal M' := fun _ ⟨s, hs, hx⟩ => ⟨s, hs, h hx⟩

theorem localization_localization₂ (Q : HeightOneSpectrum (𝓞 E)) (M : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (localization₂ Q.asIdeal M) = localization₂ Q.asIdeal M := by
  refine le_antisymm ?_ fun x hx => ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩
  rintro x ⟨s, hs, t, ht, hx⟩
  exact ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, by rwa [mul_smul]⟩

theorem mem_of_locP {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

theorem exists_idem (S : Finset (HeightOneSpectrum (𝓞 E))) {a : 𝓞 E} (ha : a ≠ 0) :
    ∃ r : 𝓞 E, (∀ P ∈ S, ∃ s, s ∉ P.asIdeal ∧ a ∣ s * (r - 1)) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ∃ s, s ∉ Q.asIdeal ∧ a ∣ s * r := by
  classical

  have key : ∀ I : Ideal (𝓞 E), I ≠ ⊥ → ∃ J₁ J₂ : Ideal (𝓞 E), I = J₁ * J₂ ∧ (∀ P ∈ S, ¬ J₂ ≤ P.asIdeal) ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → ¬ J₁ ≤ Q.asIdeal := by
    intro I
    induction I using UniqueFactorizationMonoid.induction_on_prime with
    | h₁ => intro h; exact absurd rfl h
    | h₂ u hu =>
      intro _
      rw [Ideal.isUnit_iff] at hu
      exact ⟨⊤, ⊤, by simp [hu], fun P _ h => P.isPrime.ne_top (top_le_iff.1 h), fun P _ h => P.isPrime.ne_top (top_le_iff.1 h)⟩
    | h₃ I p hI hp ih =>
      intro _
      obtain ⟨J₁, J₂, rfl, h1, h2⟩ := ih hI
      let P₀ : HeightOneSpectrum (𝓞 E) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
      have hmax : ∀ Q : HeightOneSpectrum (𝓞 E), p ≤ Q.asIdeal → Q = P₀ := fun Q h =>
        HeightOneSpectrum.ext (P₀.isMaximal.eq_of_le Q.isPrime.ne_top h).symm
      by_cases hS : P₀ ∈ S
      · refine ⟨p * J₁, J₂, by ring, h1, fun Q hQ h => ?_⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hQ (hmax Q h ▸ hS)
        · exact h2 Q hQ h
      · refine ⟨J₁, p * J₂, by ring, fun Q hQ h => ?_, h2⟩
        rcases (Q.isPrime.mul_le).1 h with h | h
        · exact hS (hmax Q h ▸ hQ)
        · exact h1 Q hQ h
  obtain ⟨J₁, J₂, hJ, h1, h2⟩ := key (Ideal.span {a}) (by simpa using ha)
  have hsup : J₁ ⊔ J₂ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let Q : HeightOneSpectrum (𝓞 E) :=
      ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
    by_cases hQ : Q ∈ S
    · exact h1 Q hQ (le_sup_right.trans hle)
    · exact h2 Q hQ (le_sup_left.trans hle)
  obtain ⟨u, hu, r, hr, hur⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : 𝓞 E) ∈ J₁ ⊔ J₂)
  refine ⟨r, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h1 P hP)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ, show s * (r - 1) = (-u) * s by rw [← hur]; ring]
    exact Ideal.mul_mem_mul (J₁.neg_mem hu) hs
  · obtain ⟨s, hs, hs'⟩ := SetLike.not_le_iff_exists.1 (h2 Q hQ)
    refine ⟨s, hs', Ideal.mem_span_singleton.1 ?_⟩
    rw [hJ]
    exact Ideal.mul_mem_mul hs hr

theorem Full.approx {M : Submodule (𝓞 E) W} (hM : Full M) (S : Finset (HeightOneSpectrum (𝓞 E))) (x : W) :
    ∃ t : W, (∀ P ∈ S, t - x ∈ localization₂ P.asIdeal M) ∧ ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → t ∈ localization₂ Q.asIdeal M := by
  obtain ⟨n, hn, hx⟩ := hM x
  obtain ⟨r, h1, h2⟩ := exists_idem S (a := (n : 𝓞 E)) (by exact_mod_cast hn.ne')
  refine ⟨r • x, fun P hP => ?_, fun Q hQ => ?_⟩
  · obtain ⟨s, hs, k, hk⟩ := h1 P hP
    refine ⟨s, hs, ?_⟩
    rw [show s • (r • x - x) = (s * (r - 1)) • x by rw [mul_smul, sub_smul, one_smul], hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx
  · obtain ⟨s, hs, k, hk⟩ := h2 Q hQ
    refine ⟨s, hs, ?_⟩
    rw [← mul_smul, hk, mul_comm, mul_smul]
    exact M.smul_mem _ hx

theorem mem_localization_of_mem (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

theorem localization_inf (Q : HeightOneSpectrum (𝓞 E)) (M M' : Submodule (𝓞 E) W) :
    localization₂ Q.asIdeal (M ⊓ M') = localization₂ Q.asIdeal M ⊓ localization₂ Q.asIdeal M' := by
  refine le_antisymm (le_inf (localization_mono Q inf_le_left) (localization_mono Q inf_le_right)) ?_
  rintro x ⟨⟨s, hs, hx⟩, t, ht, hy⟩
  exact ⟨s * t, Q.asIdeal.primeCompl.mul_mem hs ht, by rw [mul_comm, mul_smul]; exact M.smul_mem _ hx,
    by rw [mul_smul]; exact M'.smul_mem _ hy⟩

theorem mem_localization_twist [Module E W] [IsScalarTower (𝓞 E) E W] (M : Submodule (𝓞 E) W) {c : ℕ} (hc : 0 < c)
    {e : HeightOneSpectrum (𝓞 E) → ℤ} (he : ∀ Q, -1 ≤ e Q ∧ e Q ≤ 1) (Q : HeightOneSpectrum (𝓞 E)) (x : W) :
    x ∈ localization₂ Q.asIdeal (twist₂ M c e) ↔ ((c : E) ^ e Q)⁻¹ • x ∈ localization₂ Q.asIdeal M := by
  have hmem : ∀ y : W, y ∈ twist₂ M c e ↔ ∀ Q' : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q')⁻¹ • y ∈ localization₂ Q'.asIdeal M := fun y => by
    simp [twist₂, Submodule.mem_iInf]
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc.ne'
  constructor
  · rintro ⟨s, hs, hx⟩
    rw [← localization_localization₂]
    exact ⟨s, hs, by rw [smul_comm]; exact (hmem _).1 hx Q⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot Q.ne_bot
    obtain ⟨r, h1, h2⟩ := exists_idem {Q} (a := (c : 𝓞 E) ^ 2 * p)
      (mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hc.ne')) hp0)
    obtain ⟨t, ht, k, hk⟩ := h1 Q (Finset.mem_singleton_self Q)
    have hr : r ∉ Q.asIdeal := fun hr => by
      have h3 : t * (r - 1) ∈ Q.asIdeal := hk ▸ Q.asIdeal.mul_mem_right _ (Q.asIdeal.mul_mem_left _ hp)
      have h4 := (Q.isPrime.mem_or_mem h3).resolve_left ht
      exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Q.asIdeal.sub_mem hr h4))
    refine ⟨r * s, Q.asIdeal.primeCompl.mul_mem hr hs, (hmem _).2 fun Q' => ?_⟩
    by_cases hQ : Q' = Q
    · subst hQ
      refine mem_localization_of_mem _ ?_
      rw [smul_comm, mul_smul]
      exact M.smul_mem _ hx
    · obtain ⟨t', ht', k', hk'⟩ := h2 Q' (by simpa using hQ)
      obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ 2 - e Q' + e Q by have := he Q; have := he Q'; omega)
      refine ⟨t', ht', ?_⟩
      have h5 : t' • ((c : E) ^ e Q')⁻¹ • (r * s) • x = ((c : 𝓞 E) ^ m * (p * k')) • s • ((c : E) ^ e Q)⁻¹ • x := by
        have h6 := congrArg (algebraMap (𝓞 E) E) hk'
        have h7 : (c : E) ^ m = (c : E) ^ 2 * ((c : E) ^ e Q')⁻¹ * (c : E) ^ e Q := by
          rw [← zpow_natCast, ← hm, zpow_add₀ hcE, zpow_sub₀ hcE, div_eq_mul_inv, zpow_ofNat]
        simp only [map_mul, map_pow, map_natCast] at h6
        simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul, map_pow, map_natCast]
        congr 1
        rw [h7]
        have := zpow_ne_zero (e Q) hcE
        have := zpow_ne_zero (e Q') hcE
        field_simp
        linear_combination (algebraMap (𝓞 E) E s) * h6
      rw [h5]
      exact M.smul_mem _ hx

theorem expS_bound [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    -1 ≤ expS S Q ∧ expS S Q ≤ 1 := by
  unfold expS
  split_ifs <;> omega

def cosSum {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (ι : W →+ V) (As L : Submodule (𝓞 E) W)
    (θ : V → ℂ) (Ξ : W → ℂ) (z : V) : ℂ :=
  latSum As L fun t => Ξ t * (α (ι t) * opU H (-(ι t)) θ z)

def volExp {a b : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : Submodule (𝓞 E) (Sp E a)) (N' : Submodule (𝓞 E) (Sp E b)) : ℤ :=
  (b : ℤ) * ordDet P N - (a : ℤ) * ordDet P N'

end Loc

section Ambient

variable {X : Fields} (A : Amb X) {a b : ℕ}

abbrev lam (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : AddSubgroup (VCx X.Tau a b) :=
  LamC (X.embC A.σ₀) A.δ A.AA N N'

def vac (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : VCx X.Tau a b → ℂ :=
  fun z => (A.chiF a b N N')⁻¹ * A.e a b N N' z


variable (a b) in
def Moves : Prop :=
  A.δ ≠ 0 ∧ Nonempty X.Tau ∧ A.AA.FG ∧ A.AA ≠ ⊥ ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    A.chiF a b N N' ≠ 0 ∧ vac A N N' ∈ Th (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') ∧
      LaFacts (X.embC A.σ₀) A.δ A.d A.sc A.AA N N') ∧
  (∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' N'' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' → IsSdLat N'' →
    vac A N N'' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N N'') (vac A N N')) ∧
  ∀ (N N₁ : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N₁ → IsSdLat N' →
    vac A N₁ N' = inter (Formalism.L2.Ker.HV A.sc) (alV A.d A.sc) (lam A N N') (lam A N₁ N') (vac A N N')

end Ambient

theorem isHerm_HV {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) : IsHerm (Formalism.L2.Ker.HV (ι := ι) (a := a) (b := b) sc) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Formalism.L2.Ker.HV, map_sum, mul_comm]

theorem embH_injective {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] [Nonempty ι] {a b : ℕ}
    (emb : ι → E →+* ℂ) {δ : ℂ} (hδ : δ ≠ 0) : Function.Injective (embH (a := a) (b := b) emb δ) := by
  intro x y h
  obtain ⟨τ⟩ := ‹Nonempty ι›
  refine LinearMap.pi_ext' fun j => LinearMap.ext_ring (funext fun i => ?_)
  have := congrFun (congrFun (congrFun h τ) i) j
  exact (emb τ).injective (by simpa [embH, hδ] using this)

end GlobalTheory.ThetaMove
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.MomT

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable

section Inputs

open Formalism.MainNotions.TaylorLogMetric

def goodLifts (D : D7) (T : Tor D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (VC D N N') :=
  AddSubgroup.closure {y | ∃ κ : 𝓞 D.host.K,
    ‖lamC lam (D.host.φ₀ (D.host.conj ((κ : D.host.K) : D.host.E)))‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
    ∃ x ∈ La D T L L', y = (D.host.φ₀ ((κ : D.host.K) : D.host.E) * (N₀ : ℂ) / (p : ℂ) ^ n) • x}

def MomentsAt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    (Ω : ℂ_[p]) : Prop :=
  ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
    admitted D N N' L L' → ∀ t : VC D N N', TorsPrime D p (La D (tor0 D cc δ) L L') t →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
    ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), NNBasis D (tor0 D cc δ) δ p L L' b →
    ∃ μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p], ‖μ‖ ≤ 1 ∧
      ∀ (n : ℕ), ∀ y ∈ goodLifts D (tor0 D cc δ) lam N₀ n L L',
        CoefIn D (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L'))) Qbar ∧
        ∀ (m : ℕ) (y' : Fin m → Matrix (Fin N') (Fin N) D.host.E) (g : C(Fin r → ℤ_[p], ℂ_[p])),
          (∀ a : Fin r → ℕ, g (fun i => (a i : ℤ_[p])) =
            lamC lam (kap D (tor0 D cc δ) (δ • embV D (tor0 D cc δ) (∑ i, (a i : D.host.E) • b i)) y) *
              ∏ j, pairN D lam Ω b (y' j) fun i => (a i : ℤ_[p])) →
          jet D lam y' (pSer D lam (Wop D (tor0 D cc δ) p y (U D (tor0 D cc δ) t (e N N' L L')))) = μ g

def MovesAll : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ

def LatticeFactsAll : Prop :=
  ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ)
    (cD : D.what₂.Tau → ℂ), X.Ok → s.Ok → IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ →
    ∀ a b : ℕ, Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b

end Inputs

section Ops

variable {X : Fields} (A : Amb X) {a b : ℕ}

def emb (x : HomE X.E a b) : VCx X.Tau a b := embH (X.embC A.σ₀) A.δ x

def Wx (x : HomE X.E a b) (F : VCx X.Tau a b → ℂ) : VCx X.Tau a b → ℂ :=
  fun z => alV A.d A.sc (emb A x) * opU (HV A.sc) (emb A x) F z

def imH (x y : HomE X.E a b) : ℝ := altE (HV A.sc) (emb A x) (emb A y)

def coc (x y : HomE X.E a b) : ℝ := (Real.sqrt A.d * (HV A.sc (emb A x) (emb A y)).re + imH A x y) / 2

def brkE (y t : HomE X.E a b) : ℂ := brk (HV A.sc) (emb A y) (emb A t)

abbrev per (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  perO A.AA N N'

def smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) : Submodule (𝓞 X.E) (HomE X.E a b) :=
  M.map ((r • (LinearMap.id : HomE X.E a b →ₗ[X.E] HomE X.E a b)).restrictScalars (𝓞 X.E))

theorem mem_smulLat (r : X.E) (M : Submodule (𝓞 X.E) (HomE X.E a b)) (y : HomE X.E a b) :
    y ∈ smulLat r M ↔ ∃ m ∈ M, r • m = y := Iff.rfl


variable (a b) in
def PtMom {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]) (v : X.E) : Prop :=
  ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
    ∀ t : HomE X.E a b, (∃ n : ℕ, Nat.Coprime n p ∧ (n : X.E) • t ∈ per A N N') →
    ∃ N₀ : ℕ, Nat.Coprime N₀ p ∧
      (∀ y ∈ per A N N', ∀ m, jetC A.cD (Wx A (((N₀ : X.E) * v) • y) (Wx A t (A.e a b N N'))) m ∈ TaylorLogMetric.Qbar) ∧
      InIntClosure (per A N N' : Set (HomE X.E a b))
        (fun x (k : HomE X.E a b × (DVar X.Tau a b →₀ ℕ)) =>
          TaylorLogMetric.lamC lam (brkE A (((N₀ : X.E) * v) • k.1) x) * ptTab ι un x k.2)
        {k | k.1 ∈ per A N N'}
        fun k => TaylorLogMetric.lamC lam (jetC A.cD (Wx A (((N₀ : X.E) * v) • k.1) (Wx A t (A.e a b N N'))) k.2)


variable (a b) in
def Ctx (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) : Prop :=
  X.Ok ∧ A.LaHyp a b S ∧ A.AAUnit (divs (X.conjO ϖ)) ∧ A.ESmooth a b ∧ p.Prime ∧ ϖ * X.conjO ϖ = (p : 𝓞 X.E) ∧
    IsCoprime ϖ (X.conjO ϖ) ∧ (∀ P, P ∈ S ↔ ϖ ∈ P.asIdeal ∨ P ∈ SG) ∧ (∀ P ∈ SG, (p : 𝓞 X.E) ∉ P.asIdeal) ∧
    Nat.Coprime g p ∧ Nat.Coprime cA p

end Ops

section Clo

variable {p : ℕ} [Fact p.Prime] {H I : Type}

theorem clo_zero (Sup : Set H) (tab : H → I → ℂ_[p]) (M : Set I) : InIntClosure Sup tab M fun _ => 0 := by
  intro F _ ε hε
  exact ⟨0, by simp, by simp, by simpa using fun _ _ => hε⟩

theorem clo_add {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (h' : InIntClosure Sup tab M J') : InIntClosure Sup tab M fun m => J m + J' m := by
  classical
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F hF ε hε
  obtain ⟨c', hc', hc1', hcF'⟩ := h' F hF ε hε
  refine ⟨c + c', ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    rcases Finset.mem_union.1 (Finsupp.support_add (Finset.mem_coe.1 hx)) with h | h
    exacts [hc h, hc' h]
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hc1 x) (hc1' x))
  · rw [Finsupp.sum_add_index' (by simp) (by intros; ring)]
    have : J m + J' m - ((c.sum fun x r => r * tab x m) + c'.sum fun x r => r * tab x m) =
        (J m - c.sum fun x r => r * tab x m) + (J' m - c'.sum fun x r => r * tab x m) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hcF m hm) (hcF' m hm))

theorem clo_sum {κ : Type} {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} (s : Finset κ) (J : κ → I → ℂ_[p])
    (h : ∀ k ∈ s, InIntClosure Sup tab M (J k)) : InIntClosure Sup tab M fun m => ∑ k ∈ s, J k m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using clo_zero Sup tab M
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    exact clo_add (h k (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem clo_congr {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {M M' : Set I} {J J' : I → ℂ_[p]}
    (h : InIntClosure Sup tab M J) (hS : Sup ⊆ Sup') (hM : M' ⊆ M) (hJ : ∀ m ∈ M', J' m = J m) :
    InIntClosure Sup' tab M' J' := by
  intro F hF ε hε
  obtain ⟨c, hc, hc1, hcF⟩ := h F (hF.trans hM) ε hε
  exact ⟨c, hc.trans hS, hc1, fun m hm => by rw [hJ m (hF hm)]; exact hcF m hm⟩

theorem clo_comb {I' κ : Type} {Sup Sup' : Set H} {tab : H → I → ℂ_[p]} {tab' : H → I' → ℂ_[p]} {M : Set I} {M' : Set I'}
    {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J) (s : Finset κ) (r : κ → I' → ℂ_[p]) (φ : κ → I' → I)
    (hφ : ∀ k ∈ s, ∀ m ∈ M', φ k m ∈ M) (w : H → ℂ_[p]) (hw : ∀ x ∈ Sup, ‖w x‖ ≤ 1) (hw0 : ∀ x ∈ Sup, x ∉ Sup' → w x = 0)
    (htab : ∀ x ∈ Sup, ∀ m ∈ M', ∑ k ∈ s, r k m * tab x (φ k m) = w x * tab' x m) :
    InIntClosure Sup' tab' M' fun m => ∑ k ∈ s, r k m * J (φ k m) := by
  classical
  intro F hF ε hε
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ k ∈ s, ∀ m ∈ F, ‖r k m‖ ≤ C := by
    refine ⟨1 + ∑ q ∈ s ×ˢ F, ‖r q.1 q.2‖, by positivity, fun k hk m hm => ?_⟩
    have := Finset.single_le_sum (f := fun q : κ × I' => ‖r q.1 q.2‖) (fun _ _ => norm_nonneg _)
      (Finset.mk_mem_product hk hm)
    linarith
  obtain ⟨c, hc, hc1, hcF⟩ := h ((s ×ˢ F).image fun q => φ q.1 q.2) (by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hi)
    exact hφ _ (Finset.mem_product.1 hq).1 _ (hF (Finset.mem_product.1 hq).2)) (ε / 2 / C) (by positivity)
  have hmem : ∀ x, c x ≠ 0 → x ∈ Sup := fun x hx => hc (Finsupp.mem_support_iff.2 hx)
  refine ⟨Finsupp.onFinset c.support (fun x => c x * w x) (fun x hx => Finsupp.mem_support_iff.2 (left_ne_zero_of_mul hx)),
    ?_, fun x => ?_, fun m hm => ?_⟩
  · intro x hx
    have hx' : c x * w x ≠ 0 := by simpa using hx
    by_contra hn
    exact hx' (by rw [hw0 x (hmem x (left_ne_zero_of_mul hx')) hn, mul_zero])
  · rw [Finsupp.onFinset_apply]
    by_cases hx : c x = 0
    · simp [hx]
    · rw [norm_mul]; exact mul_le_one₀ (hc1 x) (norm_nonneg _) (hw x (hmem x hx))
  · rw [Finsupp.onFinset_sum _ (by simp)]
    have e : ∑ k ∈ s, r k m * J (φ k m) - ∑ x ∈ c.support, c x * w x * tab' x m =
        ∑ k ∈ s, r k m * (J (φ k m) - c.sum fun x q => q * tab x (φ k m)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finsupp.sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [mul_assoc, ← htab x (hc hx) m (hF hm), Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (C := ε / 2) (by positivity) fun k hk => ?_)
      (by linarith)
    rw [norm_mul]
    have h1 := hcF (φ k m) (Finset.mem_image.2 ⟨(k, m), Finset.mk_mem_product hk hm, rfl⟩)
    calc _ ≤ C * (ε / 2 / C) := mul_le_mul (hC k hk m hm) h1.le (norm_nonneg _) hC0.le
      _ = ε / 2 := by field_simp

theorem clo_smul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r c : ℂ_[p]) (hc : c ≠ 0) (hr : ‖r‖ ≤ ‖c‖) :
    InIntClosure Sup (fun x m => c * tab x m) M fun m => r * J m := by
  have := clo_comb (Sup' := Sup) (tab' := fun x m => c * tab x m) (M' := M) h ({()} : Finset Unit) (fun _ _ => r) (fun _ m => m)
    (fun _ _ _ hm => hm) (fun _ => r / c)
    (fun _ _ => by rw [norm_div]; exact div_le_one_of_le₀ hr (norm_nonneg _)) (fun _ h h' => absurd h h')
    (fun x _ m _ => by simp only [Finset.sum_singleton]; field_simp)
  simpa using this

theorem clo_mul {Sup : Set H} {tab : H → I → ℂ_[p]} {M : Set I} {J : I → ℂ_[p]} (h : InIntClosure Sup tab M J)
    (r : ℂ_[p]) (hr : ‖r‖ ≤ 1) : InIntClosure Sup tab M fun m => r * J m := by
  simpa using clo_smul h r 1 one_ne_zero (by simpa using hr)

end Clo

end GlobalTheory.MomT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.Proof.NarrowJetMoments

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Notions

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}


variable {ST SG SG' : Finset (HeightOneSpectrum (𝓞 E))}

end Notions

section Closure

variable {p : ℕ} [Fact p.Prime]

variable {X : Fields} {a b : ℕ}

end Closure

section Data

variable {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
  {N : Submodule (𝓞 E) (Sp E a)} {N' : Submodule (𝓞 E) (Sp E b)}

end Data

section Datum

variable {X : Fields} {a b : ℕ} {SB Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {T cA cB' : ℕ}
  {N : Submodule (𝓞 X.E) (Sp X.E a)} {N' : Submodule (𝓞 X.E) (Sp X.E b)} {w : HeightOneSpectrum (𝓞 X.K)}

variable (A : Amb X)

end Datum

section Clause

variable {X : Fields} (A : Amb X) (Pr : Primes X) (u : Pr.Word) {p : ℕ} [Fact p.Prime] (w : HeightOneSpectrum (𝓞 X.K))
  (ι : X.K →+* ℂ_[p]) (uu : X.Tau → ℂ_[p]) {a b : ℕ} (SB Sall : Finset (HeightOneSpectrum (𝓞 X.E)))
  {SG SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := a) (ST := Pr.vT u) (SG := SG)) (d' : DecoSet (E := X.E) (n := b) (ST := Pr.vT u) (SG := SG'))

end Clause

section Bad

variable {E : Type} [Field E] [NumberField E]

theorem notMem_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (P : HeightOneSpectrum (𝓞 E)) (hn : (n : 𝓞 E) ∈ P.asIdeal) :
    (m : 𝓞 E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨x, y, e⟩ := Nat.isCoprime_iff_coprime.2 h
  have e' : (x : 𝓞 E) * (m : 𝓞 E) + (y : 𝓞 E) * (n : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) e
  refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
  rw [← e']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm) (Ideal.mul_mem_left _ _ hn)

variable {X : Fields}

theorem conjP_ne_self_of_split (hX : X.Ok) {v : HeightOneSpectrum (𝓞 X.F)} (hs : SplitAt X.E v) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P.asIdeal.under (𝓞 X.F) = v.asIdeal) : conjPrime₂ P ≠ P := by
  intro hc
  have hne : GlobalTheory.MuConj.starAlg hX.star_F ≠ 1 := by
    intro h
    obtain ⟨τ⟩ : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos
    refine hX.emb_ne τ τ (RingHom.ext fun x => ?_)
    have : star x = x := congrArg (fun σ : X.E ≃ₐ[X.F] X.E => σ x) h
    show X.emb τ x = X.emb τ (star x)
    rw [this]
  have key : ∀ Q : HeightOneSpectrum (𝓞 X.E), Ideal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) v.asIdeal ≤ Q.asIdeal → Q = P := by
    intro Q hQ
    have hu : Q.under (𝓞 X.F) = P.under (𝓞 X.F) := by
      refine HeightOneSpectrum.ext ?_
      show Q.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)
      rw [hP]
      exact (v.isMaximal.eq_of_le (Q.under (𝓞 X.F)).isPrime.ne_top (Ideal.map_le_iff_le_comap.1 hQ)).symm
    rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.MuConj.starAlg hX.star_F) hX.rankE hne P Q).1 hu with h | h
    · exact h
    · rw [GlobalTheory.Mem.Chr.conjPl_iff_mem] at h
      rw [← hc]
      ext y
      rw [mem_conjP]
      exact (h (cO X.E y) y (star_star (y : X.E)).symm).symm
  obtain ⟨Q, Q', hQ, hm⟩ := hs
  exact hQ ((key Q (hm ▸ Ideal.mul_le_left)).trans (key Q' (hm ▸ Ideal.mul_le_right)).symm)

variable {Pr : Primes X}

variable {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem mem_vGs_iff {P : HeightOneSpectrum (𝓞 X.E)} : P ∈ Pr.vGs ↔ ∃ i, P ∈ Pr.vG i := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union, Fin.exists_fin_two]

theorem g_mem (hPr : Pr.Ok) {i : Fin 2} {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ Pr.vG i) : (Pr.g i : 𝓞 X.E) ∈ P.asIdeal := by
  rw [← hPr.piG_norm i]
  exact Ideal.mul_mem_left _ _ (decoFin_mem_of_mem_divs h)

theorem notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {l : ℕ} (hl : l.Prime) (hS : l ∈ S) (hg : ∀ i, l ≠ Pr.g i)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_coprime ((Nat.coprime_primes hl (hPr.g_prime i)).2 (hg i)) P (g_mem hPr hi)
  · exact notMem_of_mem_QE hsel h hl hS

theorem natCast_mem_conjP {P : HeightOneSpectrum (𝓞 X.E)} {n : ℕ} :
    (n : 𝓞 X.E) ∈ (conjPrime₂ P).asIdeal ↔ (n : 𝓞 X.E) ∈ P.asIdeal := by
  rw [mem_conjP, map_natCast]

theorem conjP_notMem_rowSG (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : conjPrime₂ P ∉ rowSG Pr sel mu := by
  classical
  intro hP'
  rcases Finset.mem_union.1 hP with h | h <;> rcases Finset.mem_union.1 hP' with h' | h'
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    obtain ⟨j, hj⟩ := mem_vGs_iff.1 h'
    by_cases hij : i = j
    · subst hij
      have h1 : X.conjO (Pr.piG i) ∈ P.asIdeal := decoFin_mem_of_mem_divs hi
      have h2 : cO X.E (cO X.E (Pr.piG i)) ∈ P.asIdeal :=
        (decoFin_mem_of_mem_divs hj : X.conjO (Pr.piG i) ∈ (conjPrime₂ P).asIdeal)
      rw [cO_cO] at h2
      obtain ⟨x, y, e⟩ := hPr.piG_cop i
      refine (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top ?_
      rw [← e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h1)
    · have hne : Pr.g i ≠ Pr.g j := by
        have := hPr.g_ne
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      exact notMem_of_coprime ((Nat.coprime_primes (hPr.g_prime i) (hPr.g_prime j)).2 hne) P
        (natCast_mem_conjP.1 (g_mem hPr hj)) (g_mem hPr hi)
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h
    exact notMem_of_mem_QE hsel h' (hPr.g_prime i) (hS i) (natCast_mem_conjP.2 (g_mem hPr hi))
  · obtain ⟨i, hi⟩ := mem_vGs_iff.1 h'
    exact notMem_of_mem_QE hsel h (hPr.g_prime i) (hS i) (natCast_mem_conjP.1 (g_mem hPr hi))
  · obtain ⟨v, hv, e⟩ := good_of_mem_QE h
    obtain ⟨v', -, e'⟩ := good_of_mem_QE h'
    have hvv : v' = v := by
      ext y
      rw [← hsel v, ← hsel v', e, e', Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP]
      have : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) y) = algebraMap (𝓞 X.F) (𝓞 X.E) y :=
        RingOfIntegers.ext (hX.star_F (y : X.F))
      rw [this]
    subst hvv
    exact conjP_ne_self_of_split hX hv.1 (e ▸ hsel v') (e'.symm.trans e)

end Bad

theorem mem_Sall {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∨ P ∈ rowSG Pr sel mu := by
  classical
  unfold Sall
  rw [Finset.mem_union]

end GlobalTheory.Proof.NarrowJetMoments
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

namespace GlobalTheory.LvT.Inh.ResFin

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

end GlobalTheory.LvT.Inh.ResFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PlacesOverConjPrimes
noncomputable section

namespace GlobalTheory.LvT.Inh

open Formalism.BasicNotions Classical NumberField IsDedekindDomain Matrix GlobalTheory.LvT GlobalTheory.LvT.Inh
open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk CSpan IntSpan wSh)
open Formalism.L2.Col (conjPrime₂ PosStar hStd UF Sp)

theorem mem_valO_of_below {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L)
    (W : HeightOneSpectrum (𝓞 L)) (Q : HeightOneSpectrum (𝓞 K))
    (h : ∀ r : 𝓞 K, r ∈ Q.asIdeal ↔ RingOfIntegers.mapRingHom j r ∈ W.asIdeal) (x : K) :
    j x ∈ valO W ↔ x ∈ valO Q := by
  letI : Algebra K L := j.toAlgebra
  haveI : W.asIdeal.LiesOver Q.asIdeal := ⟨Ideal.ext fun r => h r⟩
  rw [mem_valO, mem_valO, show j x = algebraMap K L x from rfl,
    ← HeightOneSpectrum.valuation_liesOver L Q W x]
  exact pow_le_one_iff (Ideal.ramificationIdx_pos_of_isDedekindDomain' W.asIdeal Q.ne_bot).ne'

theorem mem_Ow_iff_valO (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) : x ∈ Ow D w ↔ x ∈ valO (D.plEq w) :=
  D.val_nonneg_iff w x

theorem resChar_mem_plEq (D : D7) (w : D.what₂.places.Pl) :
    ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  rw [← (D.plEq w).valuation_lt_one_iff_mem (K := D.what₂.LL), D.val_resChar', ← WithZero.exp_zero,
    WithZero.exp_lt_exp]
  have := D.what₂.places.ramIdx_pos w
  omega

theorem resChar_eq_of_mem_plEq (D : D7) (w : D.what₂.places.Pl) {T : ℕ} (hT : T.Prime)
    (h : (T : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal) : D.what₂.places.resChar w = T := by
  by_contra hne
  have hc : IsCoprime ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) (T : 𝓞 D.what₂.LL) :=
    Nat.Coprime.cast ((Nat.coprime_primes (D.what₂.places.resChar_prime w) hT).2 hne)
  obtain ⟨a, b, hab⟩ := hc
  refine (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
  rw [← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (resChar_mem_plEq D w)) (Ideal.mul_mem_left _ _ h)

end GlobalTheory.LvT.Inh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SubDSharpInDeg
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

noncomputable section

namespace GlobalTheory.JetDeg

theorem algHom_hom {K σ ρ M N : Type} [CommRing K] [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : ρ → N)
    (g : M →+ N) (φ : MvPolynomial σ K →ₐ[K] MvPolynomial ρ K)
    (hφ : ∀ v, IsWeightedHomogeneous w' (φ (X v)) (g (w v))) {f : MvPolynomial σ K} {d : M}
    (hf : IsWeightedHomogeneous w f d) : IsWeightedHomogeneous w' (φ f) (g d) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun m hm => ?_
  have hd : Finsupp.weight w m = d := hf (mem_support_iff.mp hm)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod, ← hd, Finsupp.weight_apply,
    Finsupp.sum, map_sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun v _ => ?_
  rw [map_pow, map_nsmul]
  exact (hφ v).pow _

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {a b : ℕ}

def posW (a : ℕ) (τ : ι) : ι × Fin a × Fin a → ℕ := fun v => if v.1 = τ then 1 else 0

def derW (a b : ℕ) (τ : ι) : (ι × Fin b × Fin b) ⊕ DVar ι a b → ℕ :=
  Sum.elim (fun _ => 0) fun k => if k.1 = τ then 1 else 0

theorem blockEmb_hom (τ τ' : ι) (ν : Fin a → ℕ) {f : MvPolynomial (Fin a × Fin a) K}
    (hf : IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW a a) f ν) :
    IsWeightedHomogeneous (posW a τ) (Formalism.GradedWeylDivisibility.blockEmb K τ' f) (if τ' = τ then ∑ i, ν i else 0) := by
  let g : (Fin a → ℕ) →+ ℕ :=
    { toFun := fun x => if τ' = τ then ∑ i, x i else 0
      map_zero' := by simp
      map_add' := by
        intro x y
        split_ifs <;> simp [Finset.sum_add_distrib] }
  refine algHom_hom (Formalism.GradedWeylDivisibility.colW a a) (posW a τ) g _ (fun v => ?_) hf
  have h := isWeightedHomogeneous_X K (posW a τ) (τ', v)
  have e : g (Formalism.GradedWeylDivisibility.colW a a v) = posW a τ (τ', v) := by
    simp [g, Formalism.GradedWeylDivisibility.colW, posW, Pi.single_apply]
  rw [e]
  simpa [Formalism.GradedWeylDivisibility.blockEmb] using h

theorem frDet_hom (τ τ' : ι) :
    IsWeightedHomogeneous (posW a τ) (frDet K a τ') (if τ' = τ then a else 0) := by
  rw [frDet, Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have h : IsWeightedHomogeneous (posW a τ) (∏ i : Fin a, (X (τ', σ i, i) : Pol K ι a))
      (∑ _i : Fin a, if τ' = τ then 1 else 0) :=
    IsWeightedHomogeneous.prod _ _ _ fun i _ => isWeightedHomogeneous_X K (posW a τ) (τ', σ i, i)
  have e : (∑ _i : Fin a, if τ' = τ then 1 else 0) = if τ' = τ then a else 0 := by
    split_ifs <;> simp
  rw [e] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1
  · simpa [h1] using h
  · simpa [h1] using h.neg

theorem subD_hom (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (derW a b τ) (subD K ι a b P) d := by
  refine algHom_hom (posW a τ) (derW a b τ) (AddMonoidHom.id ℕ) _ (fun v => ?_) hP
  rw [subD, aeval_X]
  split_ifs with h
  · refine IsWeightedHomogeneous.sum _ _ _ fun β _ => ?_
    have := (isWeightedHomogeneous_X K (derW a b τ) (Sum.inl (v.1, β, (⟨v.2.2.1, h⟩ : Fin b)))).mul
      (isWeightedHomogeneous_X K (derW a b τ) (Sum.inr (v.1, β, v.2.1)))
    simpa [derW, posW] using this
  · exact isWeightedHomogeneous_zero _ _ _

variable [Fintype ι]

theorem VV_hom (lam : ι → DomWeight a) (τ : ι) {P : Pol K ι a} (hP : P ∈ Formalism.L2.DIV.VV K lam) :
    IsWeightedHomogeneous (posW a τ) P (∑ i, (lam τ).natW i) := by
  have : Formalism.L2.DIV.VV K lam ≤ weightedHomogeneousSubmodule K (posW a τ) (∑ i, (lam τ).natW i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨F, hF, rfl⟩
    have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => Formalism.GradedWeylDivisibility.blockEmb K τ' (F τ'))
      (fun τ' => if τ' = τ then ∑ i, (lam τ').natW i else 0) (w := posW a τ)
      fun τ' _ => blockEmb_hom τ τ' _ (hF τ').1
    simpa using h
  exact this hP

theorem sharp_hom (n : ι → ℕ) (τ : ι) {P : Pol K ι a} {d : ℕ} (hP : IsWeightedHomogeneous (posW a τ) P d) :
    IsWeightedHomogeneous (posW a τ) (sharp n P) (d + n τ * a) := by
  refine hP.mul ?_
  have h := IsWeightedHomogeneous.prod Finset.univ (fun τ' => frDet K a τ' ^ n τ')
    (fun τ' => n τ' • if τ' = τ then a else 0) (w := posW a τ)
    fun τ' _ => (frDet_hom τ τ').pow _
  simpa using h

theorem weight_derW (τ : ι) (μ : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    Finsupp.weight (derW a b τ) μ = ∑ β : Fin b, ∑ α : Fin a, μ (Sum.inr (τ, β, α)) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type (α₁ := ι) (α₂ := Fin b × Fin a), Finset.sum_eq_single τ]
  · simp [derW, Fintype.sum_prod_type]
  · intro x _ hx
    simp [derW, hx]
  · simp

theorem natW_cast (lam : DomWeight a) (i : Fin a) : (lam.natW i : ℤ) = lam.w i - lam.detShift := by
  have hi := i.2
  have h : lam.detShift ≤ lam.w i := by
    rw [DomWeight.detShift, dite_eq_left (by omega)]
    exact lam.anti (by rw [Fin.le_def]; simp only; omega)
  rw [DomWeight.natW]
  omega

end GlobalTheory.JetDeg


open GlobalTheory.JetDeg in
theorem GlobalTheory.subD_sharp_inDeg : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (a b : ℕ) (hab : a < b) (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (s s' : ι → ℤ) (n : ι → ℕ), WtCompat hab lam lam' s s' n → ∀ P ∈ Formalism.L2.DIV.VV K lam, ∀ μ ∈ (subD K ι a b (sharp n P)).support, InDeg lam s' (Finsupp.comapDomain Sum.inr μ Sum.inr_injective.injOn) := by
  classical
  intro K _ ι _ a b hab lam lam' s s' n hw P hP μ hμ τ
  have h := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ hP)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h
  simp only [Finsupp.comapDomain_apply]
  rw [h]
  push_cast
  have e : ∀ i, (lam τ).w i + s' τ = ((lam τ).natW i : ℤ) + n τ := fun i => by
    rw [GlobalTheory.JetDeg.natW_cast, hw.2.2 τ]; ring
  simp [e, Finset.sum_add_distrib, mul_comm]

end
end
