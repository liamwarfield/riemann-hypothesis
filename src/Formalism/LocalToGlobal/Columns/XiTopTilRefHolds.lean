module

public import Formalism.LocalToGlobal.Columns.MtHeckeSum

@[expose] public section

section -- merged from Formalism.LocalToGlobal.Columns.XtIntAtQpow
section -- merged from Formalism.LocalToGlobal.Columns.XtLamGvSCongr
open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section PhiS

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem xtLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hk : k₀ ≤ a) (_hr : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  have hS : ∀ M0 : ℕ → ℕ → E, (∀ p p', p < a → p' < a → IntAt P (M0 p p')) →
      redP P (∑ i ∈ Finset.range (k₀ - 1), M0 i (i + 1) +
        ∑ i ∈ Finset.range (r - k₀ - 1), M0 (k₀ + i) (k₀ + i + 1)) =
        ∑ i ∈ Finset.range (k₀ - 1), redP P (M0 i (i + 1)) +
          ∑ i ∈ Finset.range (r - k₀ - 1), redP P (M0 (k₀ + i) (k₀ + i + 1)) := by
    intro M0 hM0
    have h1 : ∀ i ∈ Finset.range (k₀ - 1), IntAt P (M0 i (i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hM0 _ _ (by omega) (by omega)
    have h2 : ∀ i ∈ Finset.range (r - k₀ - 1), IntAt P (M0 (k₀ + i) (k₀ + i + 1)) := fun i hi => by
      rw [Finset.mem_range] at hi
      exact hM0 _ _ (by omega) (by omega)
    rw [reduction_add (ciIntAt_sum _ _ h1) (ciIntAt_sum _ _ h2), redP_sum _ _ h1, redP_sum _ _ h2]
  rw [hS M' (fun p p' hp hp' => (h p p' hp hp').2.1), hS M (fun p p' hp hp' => (h p p' hp hp').1)]
  have hblk : ∀ i ∈ Finset.range j, ∀ s s' : Fin t,
      r + i * t + s.1 < a ∧ r + i * t + s'.1 < a := by
    intro i hi s s'
    rw [Finset.mem_range] at hi
    have hit : i * t + t ≤ j * t := by
      have h3 := Nat.mul_le_mul_right t (show i + 1 ≤ j by omega)
      rwa [Nat.succ_mul] at h3
    have hs := s.2
    have hs' := s'.2
    generalize i * t = u at hit ⊢
    generalize j * t = v at hit hja
    constructor <;> omega
  congr 1
  · congr 1
    congr 1
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (h _ _ (by omega) (by omega)).2.2
    · refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      exact (h _ _ (by omega) (by omega)).2.2
  · refine Finset.prod_congr rfl fun i hi => ?_
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1))
        (fun s s' => (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))
        (fun s s' => (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).1)]
    congr 1
    ext s s'
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact (h _ _ (hblk i hi s s').1 (hblk i hi s s').2).2.2


open Classical in
theorem xtPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hk : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  have hone : IntAt P (-1 : E) := ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := ⟨q, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hra : r ≤ r + (j - 1) * t := Nat.le_add_right _ _
  have imp : ∀ A B : ℕ → ℕ → E,
      (∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧ B p p' = A p p' + q * d) →
      ((∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (A p p')) ∧
        (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (A p p' / (q : E))) ∧
        (∀ p', p' < r → redP P (A p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
          (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (A p p') = 0) ∧
        (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t →
          redP P (A p p') = 0)) →
      ((∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (B p p')) ∧
        (∀ p p', r + (j - 1) * t ≤ p → p < n + c → p' < r + (j - 1) * t → IntAt P (B p p' / (q : E))) ∧
        (∀ p', p' < r → redP P (B p' p') = 1 ∧ ∀ p, p < r + (j - 1) * t → p ≠ p' →
          (r ≤ p ∨ symIdx k₀ rS p' < symIdx k₀ rS p ∨ (p' = k₀ + rS ∧ p < k₀)) → redP P (B p p') = 0) ∧
        (∀ p p', r ≤ p' → p' < r + (j - 1) * t → p < r + (j - 1) * t → (p' - r) / t < (p - r) / t →
          redP P (B p p') = 0)) := by
    intro A B hAB ⟨c1, c2, c3, c4⟩
    have hint : ∀ p p', p < n + c → p' < r + (j - 1) * t → IntAt P (B p p') := by
      intro p p' hp hp'
      obtain ⟨d, hd, he⟩ := hAB p p' hp hp'
      rw [he]
      exact (c1 p p' hp hp').add (hqI.mul hd)
    have hred : ∀ p p', p < n + c → p' < r + (j - 1) * t → redP P (B p p') = redP P (A p p') := by
      intro p p' hp hp'
      obtain ⟨d, hd, he⟩ := hAB p p' hp hp'
      rw [he, reduction_add (c1 p p' hp hp') (hqI.mul hd), reduction_mul hqI hd, redP_natCast_eq_zero hq, zero_mul, add_zero]
    refine ⟨hint, ?_, ?_, ?_⟩
    · intro p p' h1 h2 h3
      obtain ⟨d, hd, he⟩ := hAB p p' h2 h3
      rw [he, add_div, mul_div_cancel_left₀ _ hq0]
      exact (c2 p p' h1 h2 h3).add hd
    · intro p' hp'
      have hp'a : p' < r + (j - 1) * t := by omega
      have hp'n : p' < n + c := by omega
      refine ⟨by rw [hred p' p' hp'n hp'a]; exact (c3 p' hp').1, fun p hp hne hcond => ?_⟩
      rw [hred p p' (by omega) hp'a]
      exact (c3 p' hp').2 p hp hne hcond
    · intro p p' h1 h2 h3 h4
      rw [hred p p' (by omega) h2]
      exact c4 p p' h1 h2 h3 h4
  have fwd : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d := hD
  have bwd : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' + q * d := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    exact ⟨-d, hneg d hd, by rw [he]; ring⟩
  unfold LocE.PhiGS
  simp only
  split_ifs with h1 h2 h2
  · have hM := h2.1
    have hall : ∀ p p', p < r + (j - 1) * t → p' < r + (j - 1) * t →
        IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') ∧
        IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p') ∧
        redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p') =
          redP P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') := by
      intro p p' hp hp'
      have hpn : p < n + c := by omega
      refine ⟨hM p p' hpn hp', h1.1 p p' hpn hp', ?_⟩
      obtain ⟨d, hd, he⟩ := hD p p' hpn hp'
      rw [he, reduction_add (hM p p' hpn hp') (hqI.mul hd), reduction_mul hqI hd, redP_natCast_eq_zero hq, zero_mul, add_zero]
    rw [xtLamGvS_congr ψ₀ χ _ _ (by omega) hra le_rfl hall]
    congr 2
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
          LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' s.1 s'.1)
        (fun s s' => (hall _ _ s.2 s'.2).2.1),
      redP_det (Matrix.of fun s s' : Fin (r + (j - 1) * t) =>
          LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x s.1 s'.1)
        (fun s s' => (hall _ _ s.2 s'.2).1)]
    congr 1
    ext s s'
    simp only [Matrix.map_apply, Matrix.of_apply]
    exact (hall _ _ s.2 s'.2).2.2
  · exact absurd (imp _ _ bwd h1) h2
  · exact absurd (imp _ _ fwd h2) h1
  · rfl

open Classical in
theorem xtPhiGS_int (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {k₀ rS r t j c' n' c n : ℕ} (x : HomE E (n' + c') (n + c)) (h : LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x ≠ 0) :
    ∀ p p', p < n + c → p' < r + (j - 1) * t →
      IntAt P (LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p') := by
  intro p p' hp hp'
  by_contra hn
  apply h
  unfold LocE.PhiGS
  simp only
  rw [if_neg]
  intro hc
  exact hn (hc.1 p p' hp hp')

end PhiS

section Til

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem xtTilH_mem (hN : N = n + 1) (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : HeightOneSpectrum (𝓞 E)) (v : Sp E N) :
    v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w ↔
      (fun i : Fin n => v ⟨i.1, by omega⟩) ∈ d.1.at w ∧ IntAt w (v ⟨n, by omega⟩) := by
  subst hN
  have hOk := Deco.Ok.til (ST := ST) d.2 hT hG
  have htil : DecoSet.tilH (ST := ST) rfl pi d = ⟨d.1.til (ST := ST) pi, hOk⟩ := by
    show DecoSet.til (ST := ST) pi d = _
    unfold DecoSet.til
    rw [dite_eq_left hOk]
  rw [htil]
  show v ∈ localization₂ w.asIdeal (tilN d.1.N) ↔ _
  rw [mem_localization_tilN]
  rfl


open Classical in
theorem xtTilH_be (hN : N = n + 1) (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) (v : Sp E N) (hv : v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w.1) (i : Fin N) :
    (DecoSet.tilH (ST := ST) hN pi d).1.be w v i =
      if h : i.1 < n then d.1.be w (fun i : Fin n => v ⟨i.1, by omega⟩) ⟨i.1, h⟩
      else redP w.1 (v ⟨n, by omega⟩ / algebraMap (𝓞 E) E pi) := by
  subst hN
  have hOk := Deco.Ok.til (ST := ST) d.2 hT hG
  have htil : DecoSet.tilH (ST := ST) rfl pi d = ⟨d.1.til (ST := ST) pi, hOk⟩ := by
    show DecoSet.til (ST := ST) pi d = _
    unfold DecoSet.til
    rw [dite_eq_left hOk]
  rw [htil] at hv ⊢
  have hv' : v ∈ localization₂ w.1.asIdeal (tilN d.1.N) := hv
  show (if v ∈ localization₂ w.1.asIdeal (tilN d.1.N) then
      Fin.snoc (α := fun _ => 𝓞 E ⧸ w.1.asIdeal) (d.1.be w (initL E n v))
        (redP w.1 (v (Fin.last n) / algebraMap (𝓞 E) E pi)) else 0) i = _
  rw [if_pos hv']
  split_ifs with h
  · have hi : i = Fin.castSucc ⟨i.1, h⟩ := Fin.ext rfl
    conv_lhs => rw [hi, Fin.snoc_castSucc]
    rfl
  · have hi : i = Fin.last n := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
    rw [hi, Fin.snoc_last]
    rfl

end Til

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc1

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem xtEntB {q k₀ c' n' n : ℕ} (hc' : c' = 0) (x : HomE E (n' + c') (n + 0)) {p p' : ℕ} (hp : p < n) (hp' : p' < n') :
    LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' = x (Loc.eN E (n' + c') p') ⟨p, by omega⟩ := by
  subst hc'
  have hf : ∀ m s, LocE.fIdx k₀ 0 m s = s := by
    intro m s
    unfold LocE.fIdx
    split_ifs <;> omega
  simp [LocE.entB, hf, LocE.scE, Loc.atN, hp, hp']

theorem xtRes {c' n' p' : ℕ} (hp' : p' < n') :
    LinearMap.funLeft E E (Fin.castAdd c') (Loc.eN E (n' + c') p') = (Pi.single (⟨p', hp'⟩ : Fin n') (1 : E) : Sp E n') := by
  funext l
  simp [LinearMap.funLeft_apply, Loc.eN, Pi.single_apply, Fin.ext_iff]

theorem xtIntAt_qpow (q k : ℕ) : IntAt P ((q : E) ^ k) := by
  refine ⟨(q : 𝓞 E) ^ k, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simp


open Classical in
theorem xtLocal {q : ℕ} (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) {k₀ c' n' n N : ℕ} (hc' : c' = 0)
    (Φ : Loc.SF E K (n' + c') (n + 0))
    (hcongr : ∀ x x' : HomE E (n' + c') (n + 0), (∀ p p', p < n + 0 → p' < n' → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) → Φ x' = Φ x)
    (hint : ∀ x : HomE E (n' + c') (n + 0), Φ x ≠ 0 → ∀ p p', p < n + 0 → p' < n' →
      IntAt P (LocE.entB q k₀ c' n' 0 n (fun i => i + 1) (fun i => i + 1) x p p'))
    (ψ : E → K) (D : ℕ) (hD : 1 ≤ D)
    (psi_add : ∀ x y : E, IntAt P ((q : E) ^ D * x) → IntAt P ((q : E) ^ D * y) → ψ (x + y) = ψ x * ψ y)
    (psi_int : ∀ x : E, IntAt P x → ψ x = 1) (ε : ℤ)
    (prX : Sp E N →ₗ[E] Sp E (n + 0)) (lastN : Sp E N →ₗ[E] E)
    (hsplit : ∀ a : Sp E N, (∀ i, IntAt P (a i)) ↔ (∀ i, IntAt P (prX a i)) ∧ IntAt P (lastN a))
    (zA : HomE E n' N) (zB : HomE E n' (n + 0)) (ηB : Sp E n' →ₗ[E] E)
    (H : ∀ j : Fin n', ((∀ i, IntAt P (zA (Pi.single j 1) i)) ↔ (∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) ∧
      ((∀ i, IntAt P (zA (Pi.single j 1) i)) → (∀ i, redP P (prX (zA (Pi.single j 1)) i) = redP P (zB (Pi.single j 1) i)) ∧
        redP P (lastN (zA (Pi.single j 1))) = redP P (ηB (Pi.single j 1))))
    (y' : Sp E n') (hy : ∀ j, IntAt P ((q : E) * y' j)) :
    Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) =
      Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd c')) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) := by
  subst hc'
  have hone : IntAt P (-1 : E) :=
    ⟨-1, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hneg : ∀ z : E, IntAt P z → IntAt P (-z) := fun z hz => by
    rw [← neg_one_mul]
    exact hone.mul hz
  have hqI : IntAt P (q : E) := by simpa using xtIntAt_qpow (P := P) q 1
  have hεI : IntAt P (ε : E) :=
    ⟨ε, 1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hq0 : (q : E) ≠ 0 := by
    intro h0
    apply hu
    have h1 : ((q : ℕ) : 𝓞 E) = 0 := by
      apply IsFractionRing.injective (𝓞 E) E
      rw [map_natCast, h0, map_zero]
    rw [h1]
    exact Submodule.zero_mem _
  have diff : ∀ a b : E, IntAt P a → IntAt P b → redP P b = redP P a →
      IntAt P ((b - a) / (q : E)) := by
    intro a b ha hb hab
    have hba : IntAt P (b - a) := by
      rw [sub_eq_add_neg]
      exact hb.add (hneg a ha)
    have hr0 : redP P (b - a) = 0 := by
      have h1 := reduction_add hba ha
      rw [sub_add_cancel, hab] at h1
      exact (add_eq_right.1 h1.symm)
    exact ciIntAt_div hq hu hba hr0
  have eX : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        prX (zA (Pi.single ⟨p', hp'⟩ 1)) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have eY : ∀ p p' (hp : p < n) (hp' : p' < n'),
      LocE.entB q k₀ 0 n' 0 n (fun i => i + 1) (fun i => i + 1)
        (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) p p' =
        zB (Pi.single ⟨p', hp'⟩ 1) ⟨p, by omega⟩ := by
    intro p p' hp hp'
    rw [xtEntB rfl _ hp hp']
    simp only [LinearMap.comp_apply]
    rw [xtRes hp']
  have hexp : ∀ L : Sp E n' →ₗ[E] E, L y' = ∑ j, y' j * L (Pi.single j 1) := by
    intro L
    conv_lhs => rw [show y' = ∑ j, y' j • (Pi.single j (1 : E) : Sp E n') by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_smul, smul_eq_mul]
  by_cases hall : ∀ j : Fin n', ∀ i, IntAt P (zA (Pi.single j 1) i)
  · have hB := fun j => (H j).1.1 (hall j)
    have hl := fun j => ((hsplit _).1 (hall j)).2
    have hpr := fun j => ((hsplit _).1 (hall j)).1
    have hres := fun j => (H j).2 (hall j)
    rw [if_pos (show ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) from fun i => hl i),
      if_pos (show ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) from fun i => (hB i).2)]
    have hΦ : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) =
        Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) := by
      apply hcongr
      intro p p' hp hp'
      have hpn : p < n := by omega
      rw [eX p p' hpn hp', eY p p' hpn hp']
      refine ⟨_, diff _ _ ((hB ⟨p', hp'⟩).1 ⟨p, by omega⟩) (hpr ⟨p', hp'⟩ ⟨p, by omega⟩)
        ((hres ⟨p', hp'⟩).1 ⟨p, by omega⟩), ?_⟩
      field_simp
      try ring
    rw [hΦ]
    congr 1
    have hΔ : IntAt P ((lastN ∘ₗ zA) y' - ηB y') := by
      rw [hexp (lastN ∘ₗ zA), hexp ηB, ← Finset.sum_sub_distrib]
      refine ciIntAt_sum _ _ fun j _ => ?_
      have e : y' j * (lastN ∘ₗ zA) (Pi.single j 1) - y' j * ηB (Pi.single j 1) =
          ((q : E) * y' j) * (((lastN ∘ₗ zA) (Pi.single j 1) - ηB (Pi.single j 1)) / (q : E)) := by
        field_simp
        try ring
      rw [e]
      exact (hy j).mul (diff _ _ (hB j).2 (hl j) (hres j).2)
    have hqη : IntAt P ((q : E) * ηB y') := by
      rw [hexp ηB, Finset.mul_sum]
      refine ciIntAt_sum _ _ fun j _ => ?_
      rw [← mul_assoc]
      exact (hy j).mul (hB j).2
    have hD' : D = (D - 1) + 1 := by omega
    have h1 : IntAt P ((q : E) ^ D * ((ε : E) * ηB y')) := by
      have e : (q : E) ^ D * ((ε : E) * ηB y') = (ε : E) * (q : E) ^ (D - 1) * ((q : E) * ηB y') := by
        conv_lhs => rw [hD', pow_succ]
        ring
      rw [e]
      exact (hεI.mul (xtIntAt_qpow q (D - 1))).mul hqη
    have h2 : IntAt P ((q : E) ^ D * ((ε : E) * ((lastN ∘ₗ zA) y' - ηB y'))) := by
      rw [← mul_assoc, mul_comm ((q : E) ^ D), mul_assoc]
      exact hεI.mul ((xtIntAt_qpow q D).mul hΔ)
    have e : (ε : E) * (lastN ∘ₗ zA) y' = (ε : E) * ηB y' + (ε : E) * ((lastN ∘ₗ zA) y' - ηB y') := by
      ring
    rw [e, psi_add _ _ h1 h2, psi_int _ (hεI.mul hΔ), mul_one]
  · push_neg at hall
    obtain ⟨j, i, hji⟩ := hall
    have hnA : ¬ ∀ i, IntAt P (zA (Pi.single j 1) i) := fun h => hji (h i)
    have hnB : ¬ ((∀ i, IntAt P (zB (Pi.single j 1) i)) ∧ IntAt P (ηB (Pi.single j 1))) :=
      fun h => hnA ((H j).1.2 h)
    have hnS : ¬ ((∀ i, IntAt P (prX (zA (Pi.single j 1)) i)) ∧ IntAt P (lastN (zA (Pi.single j 1)))) :=
      fun h => hnA ((hsplit _).2 h)
    have L0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P ((lastN ∘ₗ zA) (Pi.single i 1)) then
          ψ ((ε : E) * (lastN ∘ₗ zA) y') else 0) = 0 := by
      by_cases hl : IntAt P (lastN (zA (Pi.single j 1)))
      · have hpx : ¬ ∀ i, IntAt P (prX (zA (Pi.single j 1)) i) := fun h => hnS ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (prX ∘ₗ zA ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eX p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    have R0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) *
        (if ∀ i : Fin n', IntAt P (ηB (Pi.single i 1)) then ψ ((ε : E) * ηB y') else 0) = 0 := by
      by_cases hl : IntAt P (ηB (Pi.single j 1))
      · have hpx : ¬ ∀ i, IntAt P (zB (Pi.single j 1) i) := fun h => hnB ⟨h, hl⟩
        push_neg at hpx
        obtain ⟨p, hp⟩ := hpx
        have h0 : Φ (zB ∘ₗ LinearMap.funLeft E E (Fin.castAdd 0)) = 0 := by
          by_contra h0
          have h3 := hint _ h0 p.1 j.1 p.2 j.2
          rw [eY p.1 j.1 (by omega) j.2] at h3
          exact hp h3
        rw [h0, zero_mul]
      · rw [if_neg (fun h => hl (h j)), mul_zero]
    rw [L0, R0]

end Loc1

end Formalism.L2.Col
end
end

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Mid

variable {E : Type} [Field E] [NumberField E] [StarRing E] {N n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem xtIntAt_piInv {w : HeightOneSpectrum (𝓞 E)} {pi : 𝓞 E} (h : pi ∉ w.asIdeal) : IntAt w ((algebraMap (𝓞 E) E pi)⁻¹) :=
  yIntAt_inv (IntAt.coe w pi) (by rw [reduction_coe]; exact mk_ne_zero h)

theorem xtMid (hN : N = n + 1) (d : DecoSet (E := E) (n := n) (ST := ∅) (SG := SG)) {pi : 𝓞 E} (hT : ∀ P : ST, cO E pi ∉ P.1.asIdeal) (hG : ∀ w : SG, pi ∉ w.1.asIdeal)
    (w : SG) (F' : Sp E N ≃ₗ[E] Sp E N) (hF' : (DecoSet.tilH (ST := ST) hN pi d).1.IsLift w F')
    (f0 : Sp E n ≃ₗ[E] Sp E n) (hf0 : d.1.IsLift w f0) (v : Sp E N) :
    ((∀ i, IntAt w.1 (F'.symm v i)) ↔
      (∀ i, IntAt w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧ IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) ∧
    ((∀ i, IntAt w.1 (F'.symm v i)) →
      (∀ i : Fin n, redP w.1 (F'.symm v ⟨i.1, by omega⟩) = redP w.1 (f0.symm (fun i : Fin n => v ⟨i.1, by omega⟩) i)) ∧
        redP w.1 (F'.symm v ⟨n, by omega⟩) = redP w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩)) := by
  set v0 : Sp E n := fun i : Fin n => v ⟨i.1, by omega⟩ with hv0def
  have hpi0 : algebraMap (𝓞 E) E pi ≠ 0 := by
    intro h
    have : pi = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    exact hG w (this ▸ zero_mem _)
  have hv1 : (∀ i, IntAt w.1 (F'.symm v i)) ↔ v ∈ (DecoSet.tilH (ST := ST) hN pi d).1.at w.1 := by
    rw [← ciMem_stdAt, ← hF'.1 (F'.symm v), LinearEquiv.apply_symm_apply]
  have hv2 : (∀ i, IntAt w.1 (f0.symm v0 i)) ↔ v0 ∈ d.1.at w.1 := by
    rw [← ciMem_stdAt, ← hf0.1 (f0.symm v0), LinearEquiv.apply_symm_apply]
  have hv3 : IntAt w.1 ((algebraMap (𝓞 E) E pi)⁻¹ * v ⟨n, by omega⟩) ↔ IntAt w.1 (v ⟨n, by omega⟩) := by
    constructor
    · intro h
      have := (IntAt.coe w.1 pi).mul h
      rwa [← mul_assoc, mul_inv_cancel₀ hpi0, one_mul] at this
    · intro h
      exact (xtIntAt_piInv (hG w)).mul h
  refine ⟨by rw [hv1, xtTilH_mem hN d hT hG w.1 v, hv2, hv3], fun hall => ?_⟩
  have hvD := hv1.1 hall
  have hbe : (DecoSet.tilH (ST := ST) hN pi d).1.be w v = redV w.1 (F'.symm v) := by
    have := hF'.2 (F'.symm v) ((ciMem_stdAt _ _).2 hall)
    rwa [LinearEquiv.apply_symm_apply] at this
  have hv0 : v0 ∈ d.1.at w.1 := ((xtTilH_mem hN d hT hG w.1 v).1 hvD).1
  have hbe0 : d.1.be w v0 = redV w.1 (f0.symm v0) := by
    have := hf0.2 (f0.symm v0) ((ciMem_stdAt _ _).2 (hv2.2 hv0))
    rwa [LinearEquiv.apply_symm_apply] at this
  constructor
  · intro i
    have h1 := xtTilH_be hN d hT hG w v hvD ⟨i.1, by omega⟩
    rw [dite_eq_left i.2, hbe] at h1
    have h2 := congrFun hbe0 i
    exact h1.trans h2
  · have h1 := xtTilH_be hN d hT hG w v hvD ⟨n, by omega⟩
    rw [dite_eq_right (lt_irrefl n), hbe] at h1
    rw [inv_mul_eq_div]
    exact h1

end Mid

section Fin

variable {X : Fields} {Pr : Primes X} {R : Ranks}

theorem xt_a_eq {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t = R.N (m2 + 1) := by
  unfold Ranks.r Ranks.N
  have h1 : R.m - 1 = m2 + 1 := by omega
  have h2 : R.k + R.m - 1 = R.k + (m2 + 1) := by omega
  rw [h1, h2]
  ring

theorem xt_a_le {m2 : ℕ} (hm : R.m = m2 + 2) : R.r + (R.m - 1) * R.t ≤ (R.N R.m - 1) + 0 := by
  rw [xt_a_eq hm]
  unfold Ranks.N
  rw [hm]
  have e : (m2 + 2) * (R.t + 1) = (m2 + 1) * (R.t + 1) + (R.t + 1) := by ring
  omega

theorem xt_cOf {m2 : ℕ} (hm : R.m = m2 + 2) : cOf R (m2 + 1) = 0 := by
  unfold cOf
  omega

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

theorem xtPhiTop_congr (hX : X.Ok) (hPr : Pr.Ok) {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x x' : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0))
    (hD : ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) → ∃ d, IntAt P d ∧
      LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p' + (qOf P : X.E) * d) :
    PhiTop Ch mu sharp m2 P x' = PhiTop Ch mu sharp m2 P x := by
  have hu := ciQ_notMem_sq hX hPr hP
  have hq := ciQ_mem P
  have hq0 : ((qOf P : ℕ) : X.E) ≠ 0 := ciQ_ne_zero hu
  have ha := xt_a_eq (R := R) hm
  have hle := xt_a_le (R := R) hm
  have hkr : R.k ≤ R.r := by unfold Ranks.r; have := R.two_le_m; omega
  unfold PhiTop
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    refine ciPhiG_congr hq hq0 _ _ false x x' ?_ ?_ (Nat.le_add_right _ _) hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')
    · unfold Ranks.r; have := R.two_le_m; omega
    · unfold Ranks.r; have := R.two_le_m; omega
  · simp only [if_true]
    exact xtPhiGS_congr hq hq0 _ _ x x' hkr hle fun p p' hp hp' => hD p p' hp (ha ▸ hp')

theorem xtPhiTop_int {m2 : ℕ} (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) (h : PhiTop Ch mu sharp m2 P x ≠ 0) :
    ∀ p p', p < (R.N R.m - 1) + 0 → p' < R.N (m2 + 1) →
      IntAt P (LocE.entB (qOf P) R.k (cOf R (m2 + 1)) (R.N (m2 + 1)) 0 (R.N R.m - 1) (fun i => i + 1) (fun i => i + 1) x p p') := by
  have ha := xt_a_eq (R := R) hm
  unfold PhiTop at h
  rw [if_pos hP] at h
  intro p p' hp hp'
  cases sharp
  · simp only [Bool.false_eq_true, if_false] at h
    exact ciPhiG_int _ _ false x h p p' hp (ha.symm ▸ hp')
  · simp only [if_true] at h
    exact xtPhiGS_int _ _ x h p p' hp (ha.symm ▸ hp')


open Classical in
theorem xtRepY_int {n : ℕ} {ST : Finset (HeightOneSpectrum (𝓞 X.E))} (d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := Pr.vGs)) (Y : Set (Sp X.E n))
    (hY : Y ∈ ybSet sel mu cst d.1.N) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) (j : Fin n) :
    IntAt P.1 ((qOf P.1 : X.E) * (d.1.liftFr ⟨P.1, hP⟩).symm (repY Y) j) := by
  obtain ⟨y, hy, rfl⟩ := hY
  have hrep : repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} ∈
      {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))} :=
    Classical.epsilon_spec (p := fun z => z ∈ {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))})
      ⟨y, by
        show y - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))
        rw [sub_self]
        exact zero_mem _⟩
  set ρ := repY {z | z - y ∈ locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}
  have h1 := (mem_locLat _ _ _ _).1 hy P
  have h2 := (mem_locLat _ _ _ _).1 hrep P
  simp only [if_pos hP, _root_.zpow_neg, zpow_one, inv_inv, zpow_zero, inv_one, one_smul] at h1 h2
  have h3 : (qOf P.1 : X.E) • ρ ∈ d.1.at P.1 := by
    have e : (qOf P.1 : X.E) • ρ = (qOf P.1 : X.E) • (ρ - y) + (qOf P.1 : X.E) • y := by rw [← smul_add, sub_add_cancel]
    rw [e]
    exact add_mem (yInt_smul_mem ciIntAt_q h2) h1
  have hl := Deco.liftFr_spec (d.2.hasLift ⟨P.1, hP⟩)
  have h4 := (hl.1 ((d.1.liftFr ⟨P.1, hP⟩).symm ((qOf P.1 : X.E) • ρ))).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3)
  have h5 := (ciMem_stdAt _ _).1 h4 j
  rwa [map_smul, Pi.smul_apply, smul_eq_mul] at h5

end Fin

end Formalism.L2.Col
