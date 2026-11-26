module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowDivRowWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabCardOfStabTie
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.AmbientLatticeAvoidance
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance

def reix (E : Type) [Field E] (n n' : ℕ) : Sp E n →ₗ[E] Sp E n' := LinearMap.pi fun l : Fin n' => atNL E n l.1

section Concrete

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))

abbrev rkTop (R : Ranks) : ℕ := (R.N R.m - 1) + 0



open Classical in
def lamTop (sharp : Bool) (P : HeightOneSpectrum (𝓞 X.E)) (h : HomE X.E (rkTop R) (rkTop R)) : X.K :=
  if P ∈ Pr.vGs then
    (if sharp then LocE.lamGBS (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h
      else LocE.lamGB (qOf P) (psi0P Ch P) (chiP Ch P) R.k R.r R.t R.m (R.N R.m - 1) 0 h)
  else LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P) R.r (R.N R.m - 1) h



abbrev Pt (u : Pr.Word) (i : ℕ) : Type := ChPt (R := R) sel mu u i × Option (L.β i) × Set (Sp X.E (R.N i))

variable (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)

end Concrete

section Global

variable {D : D7} {X : Fields} (s : Seam D X)

def ambE (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (e : TaylorLogMetric.FamE D) (dgen : D.what₂.Tau → ℂ) : Amb X where
  σ₀ := s.σ₀
  δ := δ
  d := D.host.d
  sc := (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹
  AA := Submodule.span (𝓞 X.E)
    {r | ∃ c ∈ cc, ∃ t ∈ D.host.AA0, r = s.iE.symm ((((c : 𝓞 D.host.K) : D.host.K) : D.host.E) * t)}
  cD τ := dgen (s.iT τ)
  e a b N N' z := e a b (s.lat N) (s.lat N') fun τ => z (s.iT.symm τ)
  chiF a b N N' := Base.chiFac χ a b (s.lat N) (s.lat N')


end Global

section Chain

variable {D : D7} {X : Fields} (s : Seam D X) {Pr : Primes X} (Ch : Chars X Pr D.R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr D.R (QE sel (mu : Chr X.F X.E X.K)))
  (abelian₂ : HeightOneSpectrum (𝓞 X.E) → Submodule (𝓞 X.E) (Sp X.E (rkTop D.R))) (dep : HeightOneSpectrum (𝓞 X.E) → ℕ)
  {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (v : Pr.Word)
  (rep : ∀ i, C.cls i → Pt sel mu L v i)
  (frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ)

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.AmbientLatticeAvoidance
end
end

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.WeightedChainData

noncomputable section

namespace GlobalTheory.KFormsCmp

section Cong

variable {E V : Type} [Field E] [AddCommGroup V] [Module E V]

end Cong

section Red

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}






end Red

section Primes

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}

theorem notMem_of_QE (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) {P : HeightOneSpectrum (𝓞 X.E)}
    (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) {p : ℕ} (hp : p.Prime) (hS : p ∈ S) : (p : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  intro hm
  unfold QE at hP
  split_ifs at hP with hf
  swap
  · simp at hP
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
  have hv' : v ∈ Qprime (mu : Chr X.F X.E X.K) := (Set.Finite.mem_toFinset hf).1 hv
  have hg : GoodPl X.E S v := by
    by_contra hn
    have := (Subgroup.mem_inf.1 mu.2).2
    exact hv' (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 this v) hn)
  apply hg.2.2
  have h1 : (p : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hs v, Ideal.mem_under]
    simpa using hm
  have h2 : ((p : ℕ) : 𝓞 X.F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h1
  have h3 := (ringChar.spec _ p).1 h2
  have h4 : ringChar (𝓞 X.F ⧸ v.asIdeal) = p :=
    ((Nat.dvd_prime hp).1 h3).resolve_left CharP.ringChar_ne_one
  show ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
  rwa [h4]

theorem g_mem_of_vGs (hP : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.E)} (hw : w ∈ Pr.vGs) :
    ∃ k, (Pr.g k : 𝓞 X.E) ∈ w.asIdeal := by
  classical
  rcases Finset.mem_union.1 hw with h | h
  · exact ⟨0, hP.g_mem h⟩
  · exact ⟨1, hP.g_mem h⟩

theorem disj (hP : Pr.Ok) (hs : IsSel X sel) (mu : Tup X.F X.E X.K S) (hg : ∀ k, Pr.g k ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hQ : P ∈ QE sel (mu : Chr X.F X.E X.K)) : P ∉ Pr.vGs := fun hw => by
  obtain ⟨k, hk⟩ := g_mem_of_vGs hP hw
  exact notMem_of_QE hs mu hQ (hP.g_prime k) (hg k) hk

end Primes

section Top

variable {E : Type} [Field E] {a n : ℕ}

end Top

section Levels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)



variable {T}

end Levels

section Points

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)

abbrev APt (i : ℕ) : Type := AmbientLatticeAvoidance.Pt (R := D.R) T.sel T.xi T.L T.w i


variable {T}

end Points

section Moves

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} (T : ChainData D u μ)
  (abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R)))
  (dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ)

variable {T abelian₂ dep}

end Moves

section Classes

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}


variable {rep : ∀ i, (D.chTw u μ).cls i → APt T i}


end Classes

section Kernels

variable {D : D7} {u : D.what₂.Word} {μ : D.what₂.Tup} {T : ChainData D u μ}
  {rep : ∀ i, (D.chTw u μ).cls i → APt T i}




variable {abelian₂ : HeightOneSpectrum (𝓞 T.X.E) → Submodule (𝓞 T.X.E) (Sp T.X.E (AmbientLatticeAvoidance.rkTop D.R))}
  {dep : HeightOneSpectrum (𝓞 T.X.E) → ℕ}

end Kernels

end GlobalTheory.KFormsCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdr
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsBis
namespace GlobalTheory.PolynomialNormBound

theorem main : ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {j m : ℕ}, j ≠ (0 : ℕ) → ¬l ^ m ∣ j →
    ∃ (c : ℤ_[l]), (↑j : ℤ_[l]) * c = (↑l : ℤ_[l]) ^ (m - (1 : ℕ)) := by
  intro l inst j m hj hdvd
  have hl : l.Prime := inst.out
  obtain ⟨v, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hj l hl.ne_one
  have hvm : v < m := by
    by_contra h
    exact hdvd (Dvd.dvd.mul_right (Nat.pow_dvd_pow l (not_lt.mp h)) u)
  have hunit : IsUnit (u : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl).mpr hu
  obtain ⟨w, hw⟩ := hunit
  refine ⟨(↑w⁻¹ : ℤ_[l]) * (l : ℤ_[l]) ^ (m - 1 - v), ?_⟩
  have hsplit : (l : ℤ_[l]) ^ (m - 1) = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  push_cast
  rw [← hw]
  calc (l : ℤ_[l]) ^ v * ↑w * (↑w⁻¹ * (l : ℤ_[l]) ^ (m - 1 - v))
      = (l : ℤ_[l]) ^ v * ((↑w * ↑w⁻¹) * (l : ℤ_[l]) ^ (m - 1 - v)) := by ring
    _ = (l : ℤ_[l]) ^ v * (l : ℤ_[l]) ^ (m - 1 - v) := by rw [Units.mul_inv, one_mul]

end GlobalTheory.PolynomialNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdr
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.Pst.StLat

theorem exists_mul_eq_pow_pred {l : ℕ} [Fact l.Prime] {j m : ℕ} (hj : j ≠ 0) (hm : ¬ l ^ m ∣ j) :
    ∃ c : ℤ_[l], ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ (m - 1) := by
  first
  | exact @_root_.GlobalTheory.PolynomialNormBound.main
  | exact _root_.GlobalTheory.PolynomialNormBound.main
  | (apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PolynomialNormBound.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PolynomialNormBound.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PolynomialNormBound.main ..)

theorem not_pow_dvd {l m j : ℕ} (h1 : j ≠ 0) (h2 : j < 2 * l ^ m) (h3 : j ≠ l ^ m) : ¬ l ^ m ∣ j := by
  rintro ⟨t, rfl⟩
  rcases t with _ | _ | t
  · simp at h1
  · simp at h3
  · have : l ^ m * 2 ≤ l ^ m * (t + 1 + 1) := Nat.mul_le_mul_left _ (by omega)
    omega

theorem log_trunc_pow : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) -
      e * betaD ϖ ^ (l ^ m) := by
  intro l _ ϖ hker hfil u hu m hm
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  set M := l ^ (m + 1) with hM
  set n := 2 * M with hn
  have hlpos : 0 < l := (Fact.out : l.Prime).pos
  have hMpos : 0 < M := pow_pos hlpos _
  set β := beta ϖ with hβ

  have hc : ∀ j : ℕ, ∃ c : ℤ_[l], (j ≠ 0 ∧ j < n ∧ j ≠ M) → ((j : ℕ) : ℤ_[l]) * c = (l : ℤ_[l]) ^ m := by
    intro j
    by_cases h : j ≠ 0 ∧ j < n ∧ j ≠ M
    · obtain ⟨c, hc⟩ := exists_mul_eq_pow_pred (l := l) (m := m + 1) h.1 (not_pow_dvd h.1 h.2.1 h.2.2)
      exact ⟨c, fun _ => by simpa using hc⟩
    · exact ⟨0, fun h' => (h h').elim⟩
  choose c hc using hc
  let d : ℕ → ℤ_[l] := fun j => if j = M ∨ j = n then 0 else c j
  let a : ℕ → Per.AinfP l := fun k => (-1) ^ k * Per.zP l (d (k + 1)) * β ^ (k + 1)
  let S : Per.AinfP l := ∑ k ∈ Finset.range n, a k
  let e0 : Per.AinfP l := (-1) ^ (M - 1)
  let T : Per.AinfP l := (-1) ^ (n - 1) * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
    ((n.factorial / (n - 1 + 1) : ℕ) : Per.AinfP l) * β ^ (n - 1 + 1)
  have hS : S ∈ Sa ϖ := by
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ ?_ _) ?_) (Subalgebra.pow_mem _ ?_ _)
    · exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)
    · first
      | exact Subalgebra.algebraMap_mem _ _
      | (rw [GlobalTheory.RingIface.padicIntMap_eq_algebraMap_comp]; exact Subalgebra.algebraMap_mem _ _)
    · exact Algebra.subset_adjoin (Set.mem_singleton _)

  have hterm : ∀ k ∈ Finset.range n, ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
      ((-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1)) =
      ((n.factorial : ℕ) : Per.AinfP l) * ((l : ℕ) : Per.AinfP l) * a k +
      (if k = M - 1 then ((n.factorial : ℕ) : Per.AinfP l) * ((-1) ^ k * β ^ (k + 1)) else 0) +
      (if k = n - 1 then (-1) ^ k * ((l : ℕ) : Per.AinfP l) ^ (m + 1) *
        ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) else 0) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hdvd : (k + 1) ∣ n.factorial := Nat.dvd_factorial (by omega) (by omega)
    have hq : (((n.factorial / (k + 1) : ℕ) : Per.AinfP l)) * ((k + 1 : ℕ) : Per.AinfP l) =
        ((n.factorial : ℕ) : Per.AinfP l) := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    by_cases h1 : k = M - 1
    · have h2 : ¬ k = n - 1 := by omega
      have hk1 : k + 1 = M := by omega
      have hda : d (k + 1) = 0 := by simp [d, hk1]
      rw [if_pos h1, if_neg h2]
      simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
      rw [← hq, hk1, hM, Nat.cast_pow]
      ring
    · by_cases h2 : k = n - 1
      · have hk1 : k + 1 = n := by omega
        have hda : d (k + 1) = 0 := by simp [d, hk1]
        rw [if_neg h1, if_pos h2]
        simp only [a, hda, map_zero, mul_zero, zero_mul, add_zero, zero_add]
        ring
      · have hne : ¬ (k + 1 = M ∨ k + 1 = n) := by omega
        have hda : d (k + 1) = c (k + 1) := by simp only [d, hne, if_false]
        have hck := hc (k + 1) ⟨by omega, by omega, by omega⟩
        have hck' := congrArg (Per.zP l) hck
        rw [map_mul, map_natCast, map_pow, map_natCast] at hck'
        rw [if_neg h1, if_neg h2]
        simp only [a, hda, add_zero]
        rw [← hq]
        linear_combination -(-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) *
          ((l : ℕ) : Per.AinfP l) * hck'
  have hsum : ((l : ℕ) : Per.AinfP l) ^ (m + 1) * ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : Per.AinfP l) * β ^ (k + 1) =
      ((n.factorial : ℕ) : Per.AinfP l) * (((l : ℕ) : Per.AinfP l) * S + e0 * β ^ M) + T := by
    rw [Finset.mul_sum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq', ← Finset.mul_sum]
    have hm1 : M - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    have hn1 : n - 1 ∈ Finset.range n := Finset.mem_range.2 (by omega)
    rw [if_pos hm1, if_pos hn1, Nat.sub_add_cancel (by omega : 1 ≤ M)]
    simp only [S, e0, T]
    ring
  have hβI : β ∈ Per.kerP l := by rw [hker]; exact Ideal.mem_span_singleton_self _
  have hT : T ∈ Per.kerP l ^ n := by
    have : β ^ (n - 1 + 1) ∈ Per.kerP l ^ n := by
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
      exact Ideal.pow_mem_pow hβI n
    exact Ideal.mul_mem_left _ _ this

  let s : Per.BdRp l := algebraMap (Per.AinfP l) (Per.BdRp l) S
  refine ⟨s, Subring.mem_map.2 ⟨S, hS, rfl⟩, algebraMap (Per.AinfP l) (Per.BdRp l) e0, ?_, ?_⟩
  · rcases neg_one_pow_eq_or (Per.AinfP l) (M - 1) with h | h
    · left; simp [e0, h]
    · right; simp [e0, h]
  · rw [← Ideal.mem_span_singleton, ← hfil]
    rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
    have hev : ∀ x : Per.AinfP l, Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) x) =
        Ideal.Quotient.mk _ x := fun x => GlobalTheory.RingIface.ev_alg l n x
    let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
    have hunit : IsUnit ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) := by
      have := (GlobalTheory.RingBasics.isUnit_nat l n.factorial n.factorial_ne_zero).map q
      rwa [map_natCast] at this
    have hqT : q T = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hT
    have hs2 := congrArg q hsum
    simp only [map_add (f := _), map_mul, map_pow, map_natCast, hqT, add_zero] at hs2
    have hun := hu n
    apply hunit.mul_left_cancel
    rw [mul_zero]
    simp only [betaD, map_sub, map_mul, map_pow, map_natCast, s, hev]
    change ((n.factorial : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) * (((l : ℕ) : _) * (((l : ℕ) : _) ^ m * Per.ev l n u - q S) -
      q e0 * q β ^ M) = 0
    change _ = q _ at hun
    linear_combination ((l : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ n) ^ (m + 1) * hun + hs2

end GlobalTheory.Pst.StLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogPeriodCongruenceBdrStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_period_congruence_bdr : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), Per.kerP l = Ideal.span {beta ϖ} →
  (∀ n : ℕ, Per.FilP l n = Ideal.span {betaD ϖ ^ n}) → ∀ u : Per.BdRp l, IsLogP (beta ϖ) u →
  ∀ m : ℕ, 1 ≤ m → ∃ s ∈ Sg ϖ, ∃ e : Per.BdRp l, (e = 1 ∨ e = -1) ∧
    betaD ϖ ^ (2 * l ^ m) ∣ ((l : ℕ) : Per.BdRp l) * (((l : ℕ) : Per.BdRp l) ^ (m - 1) * u - s) - e * betaD ϖ ^ (l ^ m) := by
  first | exact @GlobalTheory.Pst.StLat.log_trunc_pow | exact GlobalTheory.Pst.StLat.log_trunc_pow | (intros; apply GlobalTheory.Pst.StLat.log_trunc_pow <;> assumption)
end
end
