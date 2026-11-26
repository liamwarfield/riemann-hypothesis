module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisConjTaylorThetaTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTriple
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleRows

def cv (D : D7) {n : ℕ} (y : Fin n → D.host.E) : Fin n → D.host.E := fun j => D.host.conj (y j)

def IC (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • fun j => D.host.conj (y j)}

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ}

theorem cv_add (x y : Fin n → D.host.E) : cv D (x + y) = cv D x + cv D y := by
  funext j; simp only [cv, Pi.add_apply, map_add (f := _)]

theorem cv_smul (a : 𝓞 D.host.E) (x : Fin n → D.host.E) :
    cv D (a • x) = ((sgO D a : 𝓞 D.host.E) : D.host.E) • cv D x := by
  funext j
  rw [← algebraMap_smul D.host.E a x]
  simp only [cv, Pi.smul_apply, smul_eq_mul, map_mul, sgO_coe]

theorem smul_cv_mem {L : Lat D n} {t : D.host.E} (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) :
    t • cv D y ∈ IC D cc L := Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IC_mono {L L' : Lat D n} (h : L ≤ L') : IC D cc L ≤ IC D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem mul_int {t e : D.host.E} (ht : t ∈ Iid D cc) (he : IntE D e) : t * e ∈ Iid D cc := by
  obtain ⟨a, rfl⟩ := he
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ ht

theorem int_hE {L : Lat D n} (hL : SD D L) {x y : Fin n → D.host.E} (hx : x ∈ L) (hy : y ∈ L) :
    IntE D (hE D x y) := (((sd_iff D L).1 hL).2.2 x).1 hx y hy

theorem pair_cv (t : D.host.E) (y w : Fin n → D.host.E) : ∑ j, (t • cv D y) j * w j = t * hE D w y := by
  simp only [cv, hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem pair_mem {L : Lat D n} (hL : SD D L) {r w : Fin n → D.host.E} (hr : r ∈ IC D cc L) (hw : w ∈ L) :
    ∑ j, r j * w j ∈ Iid D cc := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    change ∑ j, (t • cv D y) j * w j ∈ _
    rw [pair_cv]
    exact mul_int ht (int_hE hL hw hy)
  | zero => simp
  | add u v _ _ hu hv =>
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    exact add_mem hu hv
  | smul a v _ hv =>
    simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum]
    exact Submodule.smul_mem _ _ hv

theorem P_smul_cv {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {p : 𝓞 D.host.E} (hp : p ∈ P) {t : D.host.E} (ht : t ∈ Iid D cc) :
    (p • t) • cv D b ∈ IC D cc M := by
  have h := smul_cv_mem ht (hb _ (hσ p hp))
  rw [cv_smul, sgO_sgO, smul_smul, mul_comm] at h
  rw [Algebra.smul_def]
  exact h

theorem decomp {M : Lat D n} {P : Ideal (𝓞 D.host.E)} (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin n → D.host.E}
    (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {r : Fin n → D.host.E}
    (hr : r ∈ IC D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, r - (a • t₀) • cv D b ∈ IC D cc M := by
  induction hr using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨a, ha⟩ := hg (sgO D o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have h1 : (sgO D o • t - a • t₀) • cv D b ∈ IC D cc M := by
      refine Submodule.smul_induction_on (p := fun s => s • cv D b ∈ IC D cc M) ha ?_ ?_
      · intro p hp s hs; exact P_smul_cv hσ hb hp hs
      · intro u v hu hv; rw [add_smul]; exact add_mem hu hv
    have h2 := add_mem (smul_cv_mem ht hm) h1
    convert h2 using 1
    change t • cv D (m + o • b) - _ = _
    rw [cv_add, cv_smul, smul_add, smul_smul, sub_smul, Algebra.smul_def (sgO D o) t, mul_comm t, add_sub_assoc]
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    convert add_mem ha ha' using 1
    rw [add_smul, add_smul]; abel
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    convert Submodule.smul_mem _ c ha using 1
    rw [smul_sub, mul_smul, smul_assoc]

def Pt (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) : (Fin N' → Fin N → D.host.E) →+ VC D N N' where
  toFun z := pt D (tor0 D cc δ) δ (Matrix.of z)
  map_zero' := by funext τ i j; simp [pt, embV, tor0]
  map_add' z w := by funext τ i j; simp [pt, embV, tor0, mul_add]

theorem Pt_apply (δ : ℂ) {N N' : ℕ} (z : Fin N' → Fin N → D.host.E) (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) :
    Pt D cc δ N N' z τ i j = δ * embT D τ (z i j) := rfl

def Row (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N : ℕ} (N' : ℕ) (t₀ : D.host.E) (b : Fin N → D.host.E)
    (i : Fin N') : 𝓞 D.host.E →+ VC D N N' where
  toFun a := Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b))
  map_zero' := by simp
  map_add' a a' := by rw [add_smul, add_smul, Pi.single_add, map_add (f := _)]

theorem Row_apply (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (i : Fin N') (a : 𝓞 D.host.E) :
    Row D cc δ N' t₀ b i a = Pt D cc δ N N' (Pi.single i ((a • t₀) • cv D b)) := rfl

theorem sum_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N → D.host.E) (a : Fin N' → 𝓞 D.host.E) :
    ∑ i, Row D cc δ N' t₀ b i (a i) = Pt D cc δ N N' (fun i => (a i • t₀) • cv D b) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Row_apply, ← map_sum]
  rw [Finset.univ_sum_single (fun i => (a i • t₀) • cv D b)]

theorem Hf_zero_left (T : Tor D) {N N' : ℕ} (y : VC D N N') : Hf D T 0 y = 0 := by simp [Hf]

theorem Hf_Row (δ : ℂ) {N N' : ℕ} (t₀ : D.host.E) (b x : Fin N → D.host.E) (i j : Fin N') (a a' : 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i a') (Row D cc δ N' t₀ b j a) =
      if i = j then Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i (a' * sgO D a)) (Row D cc δ N' t₀ b i 1) else 0 := by
  split_ifs with h
  · subst h
    simp only [Hf, Row_apply, Pt_apply]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      have e : embT D τ (algebraMap (𝓞 D.host.E) D.host.E (sgO D a)) =
          (starRingEnd ℂ) (embT D τ (algebraMap (𝓞 D.host.E) D.host.E a)) := embT_conj D τ a
      simp only [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul]
      simp only [Algebra.smul_def, map_mul, map_one, e]
      ring
    · simp [Pi.single_eq_of_ne hk]
  · simp only [Hf, Row_apply, Pt_apply]
    rw [Finset.sum_eq_zero, zero_div]
    refine fun τ _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    by_cases hk : k = i
    · subst hk
      simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hk]

theorem Pt_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (z : Fin N' → Fin N → D.host.E) :
    Pt D cc δ N N' z ∈ La D (tor0 D cc δ) L (stdL D N') ↔ ∀ i, z i ∈ IC D cc L := by
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    have : Matrix.of z = w := h1 e
    subst this
    exact (h4 L hL _).1 hw
  · intro h
    exact ⟨Matrix.of z, (h4 L hL _).2 h, rfl⟩

theorem exists_Pt {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} {v : VC D N N'}
    (hv : v ∈ La D (tor0 D cc δ) L (stdL D N')) : ∃ z, v = Pt D cc δ N N' z := by
  obtain ⟨w, -, e⟩ := ((GlobalTheory.T.thetaLattice_image_rationalHomLattice D cc δ hδ N N').2.1 L _ v).1 hv
  exact ⟨w, e⟩

theorem single_mem {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {L : Lat D N} (hL : SD D L) (i : Fin N')
    {r : Fin N → D.host.E} (hr : r ∈ IC D cc L) :
    Pt D cc δ N N' (Pi.single i r) ∈ La D (tor0 D cc δ) L (stdL D N') := by
  refine (Pt_mem hδ hL _).2 fun k => ?_
  by_cases hk : k = i
  · subst hk; rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hk]; exact zero_mem _

theorem reduce {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M L₁ L₂ : Lat D N} {P : Ideal (𝓞 D.host.E)}
    (hσ : ∀ a ∈ P, sgO D a ∈ P) {b : Fin N → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc)
    (hB : SD D (M ⊔ Submodule.span (𝓞 D.host.E) {b})) (h₁ : SD D L₁) (h₂ : SD D L₂) (m₁ : M ≤ L₁) (m₂ : M ≤ L₂) :
    ∀ z ∈ La D (tor0 D cc δ) (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (stdL D N'), ∃ a : Fin N' → 𝓞 D.host.E,
      z - ∑ i, Row D cc δ N' t₀ b i (a i) ∈
        La D (tor0 D cc δ) L₁ (stdL D N') ⊓ La D (tor0 D cc δ) L₂ (stdL D N') := by
  intro z hz
  obtain ⟨w, rfl⟩ := exists_Pt hδ hz
  choose a ha using fun i => decomp hσ hb hg ((Pt_mem hδ hB w).1 hz i)
  refine ⟨a, ?_⟩
  rw [sum_Row, ← map_sub]
  exact ⟨(Pt_mem hδ h₁ _).2 fun i => IC_mono m₁ (ha i), (Pt_mem hδ h₂ _).2 fun i => IC_mono m₂ (ha i)⟩

theorem triDat_rows : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ)
    (P : Ideal (𝓞 D.host.E)), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → ∀ A B C : Lat D N, Tri D P A B C →
    TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) A (stdL D N')) (La D (tor0 D cc δ) B (stdL D N'))
      (La D (tor0 D cc δ) C (stdL D N')) P N' := by
  intro D cc δ hcc hδ N N' P hP hσ A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hθ⟩
  obtain ⟨t₀, ht₀, hg, hq⟩ := GlobalTheory.T.exists_generator_cmDifferentIdealScaled D cc hcc P hP
  have mA : M ≤ A := eA ▸ le_sup_left
  have mB : M ≤ B := eB ▸ le_sup_left
  have mC : M ≤ C := eC ▸ le_sup_left
  have bA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hat : ∀ a : 𝓞 D.host.E, a • t₀ ∈ Iid D cc := fun a => Submodule.smul_mem _ _ ht₀
  have hsm : ∀ (p : 𝓞 D.host.E) (u v : Fin N → D.host.E), p • hE D u v = hE D (p • u) v := fun p u v => by
    rw [← algebraMap_smul D.host.E p u, hE_smul_left, Algebra.smul_def]
  refine ⟨Row D cc δ N' t₀ b, Row D cc δ N' t₀ x, fun i =>
    { toFun := fun s => Hf D (tor0 D cc δ) (Row D cc δ N' t₀ x i s) (Row D cc δ N' t₀ b i 1)
      map_zero' := by rw [map_zero, Hf_zero_left]
      map_add' := fun s s' => by rw [map_add (f := _), Hf_add_left] }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    exact Hf_Row δ t₀ b x i j a a'
  · intro i a
    refine ⟨single_mem hδ hB i (smul_cv_mem (hat a) bB), single_mem hδ hC i (smul_cv_mem (hat a) bC), ?_⟩
    rw [Row_apply, Row_apply, ← map_add (f := _), ← Pi.single_add, ← smul_add, ← cv_add]
    exact single_mem hδ hA i (smul_cv_mem (hat a) bA)
  · intro i p hpP
    have h1 := P_smul_cv hσ (fun p h => (hp p h).1) hpP ht₀
    have h2 := P_smul_cv hσ (fun p h => (hp p h).2) hpP ht₀
    exact ⟨⟨single_mem hδ hA i (IC_mono mA h1), single_mem hδ hC i (IC_mono mC h1)⟩,
      ⟨single_mem hδ hA i (IC_mono mA h2), single_mem hδ hB i (IC_mono mB h2)⟩⟩
  · subst eB
    exact reduce hδ hσ (fun p h => (hp p h).1) hg hB hA hC mA mC
  · subst eC
    exact reduce hδ hσ (fun p h => (hp p h).2) hg hC hA hB mA mB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hA ((Pt_mem hδ hA _).1 ha i) bA
    rw [pair_cv, hE_add_left, mul_add] at h1
    have h2 := sub_mem h1 (mul_int (hat (a i)) (int_hE hB bB bB))
    rw [add_sub_cancel_left, smul_mul_assoc] at h2
    refine hq (hE D x b) (fun h => hθ (conj_hE D x b ▸ h.conj)) (fun p hpP => ?_) _ h2
    rw [hsm]; exact int_hE hB (mB (hp p hpP).2) bB
  · intro a ha i
    rw [sum_Row] at ha
    have h1 := pair_mem hB ((Pt_mem hδ hB _).1 ha i) bB
    rw [pair_cv, smul_mul_assoc] at h1
    refine hq (hE D b x) hθ (fun p hpP => ?_) _ h1
    rw [hsm]; exact int_hE hC (mC (hp p hpP).1) bC

end GlobalTheory.TriangleRows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDiagonalDataOfSelfDualNeighbourTripleStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTripleDiagonalData_of_selfDualNeighbourTriple : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → (∀ a ∈ P, sgO D a ∈ P) → ∀ A B C : Lat D N, Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) A (stdL D N')) (La D (tor0 D cc δ) B (stdL D N')) (La D (tor0 D cc δ) C (stdL D N')) P N' := by
  first | exact @GlobalTheory.TriangleRows.triDat_rows | exact GlobalTheory.TriangleRows.triDat_rows | (intros; apply GlobalTheory.TriangleRows.triDat_rows <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WeilPairingGalois

theorem exists_top_agree (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (S : Set ℂ) (hS : S.Countable)
    (hM : ∀ x ∈ S, x ∈ M) :
    ∃ s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ, ∀ x ∈ S, cj ⊤ s x = cj M ρ x := by
  have hle : IntermediateField.adjoin ℚ S ≤ M := IntermediateField.adjoin_le_iff.2 hM
  haveI : Countable (IntermediateField.adjoin ℚ S) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ S).trans ?_
    have h1 : Cardinal.mk S ≤ Cardinal.aleph0 := Cardinal.le_aleph0_iff_set_countable.2 hS
    simp [h1]
  obtain ⟨τ, hτ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq (IntermediateField.adjoin ℚ S)
    (IntermediateField.adjoin ℚ S).val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨(τ.toRingHom.comp (⊤ : IntermediateField ℚ ℂ).val.toRingHom).toRatAlgHom, fun x hx => ?_⟩
  have h := hτ ⟨x, IntermediateField.subset_adjoin ℚ S hx⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos (hM x hx), dif_pos (IntermediateField.mem_top (F := ℚ) (x := x))]
  exact h

theorem cj_top_mul (s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (x y : ℂ) :
    cj ⊤ s (x * y) = cj ⊤ s x * cj ⊤ s y := by
  simp only [cj, TaylorLogMetric.liftM, dif_pos (IntermediateField.mem_top (F := ℚ))]
  rw [← map_mul]; rfl

theorem cj_one (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) : cj M ρ 1 = 1 := by
  simp only [cj, TaylorLogMetric.liftM, dif_pos M.one_mem]
  exact map_one ρ

theorem ee_add (a b : ℝ) : ee (a + b) = ee a * ee b := by
  simp only [ee, ← Complex.exp_add]; congr 1; push_cast; ring

theorem latticeRiemannForm_add_left (Λ : AddSubgroup ℂ) (x y w : ℂ) : gl3FieldFirst Λ (x + y) w = gl3FieldFirst Λ x w + gl3FieldFirst Λ y w := by
  simp only [gl3FieldFirst, add_mul, Complex.add_im, add_div]

theorem latticeRiemannForm_add_right (Λ : AddSubgroup ℂ) (x y w : ℂ) : gl3FieldFirst Λ w (x + y) = gl3FieldFirst Λ w x + gl3FieldFirst Λ w y := by
  simp only [gl3FieldFirst, map_add (f := _), mul_add, Complex.add_im, add_div]

theorem latticeRiemannForm_natCast_mul_comm (Λ : AddSubgroup ℂ) (n : ℕ) (x w : ℂ) : gl3FieldFirst Λ x (n * w) = gl3FieldFirst Λ (n * x) w := by
  simp only [gl3FieldFirst, map_mul, map_natCast]; congr 2; ring

theorem expTwoPiI_latticeRiemannForm_of_mem (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {x w : ℂ} (hx : x ∈ Λ) (hw : w ∈ Λ) : ee (gl3FieldFirst Λ x w) = 1 := by
  obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 hx)
  obtain ⟨p, q, rfl⟩ := PeriodPair.mem_lattice.1 ((h _).1 hw)
  have ha := (GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h).2.2.2.1
  have h1 : ((m * L.ω₁ + n * L.ω₂) * (starRingEnd ℂ) (p * L.ω₁ + q * L.ω₂)).im =
      ((m * q - n * p : ℤ) : ℝ) * (L.ω₁ * starRingEnd ℂ L.ω₂).im := by
    simp; ring
  have h2 : ∃ k : ℤ, gl3FieldFirst Λ (m * L.ω₁ + n * L.ω₂) (p * L.ω₁ + q * L.ω₂) = k := by
    rw [gl3FieldFirst, h1, ha]
    generalize (L.ω₁ * starRingEnd ℂ L.ω₂).im = c
    rcases lt_trichotomy c 0 with hc | hc | hc
    · refine ⟨-(m * q - n * p), ?_⟩
      rw [abs_of_neg hc]; have := hc.ne; push_cast; field_simp
    · exact ⟨0, by simp [hc]⟩
    · refine ⟨(m * q - n * p), ?_⟩
      rw [abs_of_pos hc]; have := hc.ne'; field_simp
  obtain ⟨k, hk⟩ := h2
  rw [hk, ee, Complex.exp_eq_one_iff]
  exact ⟨k, by push_cast; ring⟩

theorem value_shift (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) (x l : ℂ)
    (hG : ∀ z, U1 Λ (2 * l) G z = G z) :
    U1 Λ (x + 2 * l) G 0 = ee (gl3FieldFirst Λ x l) * U1 Λ x G 0 := by
  have h := hG x
  simp only [U1, zero_add] at h ⊢
  rw [← h, ee, gl3FieldFirst, mul_assoc (G _), ← Complex.exp_add, mul_left_comm, ← Complex.exp_add]
  congr 2
  rw [Complex.ofReal_div, Complex.im_eq_sub_conj]
  simp only [map_add (f := _), map_mul, Complex.conj_conj, map_ofNat]
  by_cases hA : (area Λ : ℂ) = 0
  · simp [hA]
  · field_simp
    ring

theorem isLattice_of_periodPair (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) :
    ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂} := by
  refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
  ext z
  rw [h, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

theorem periodPair_of_isLattice (Λ : AddSubgroup ℂ)
    (h : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}) :
    ∃ L : PeriodPair, ∀ z, z ∈ Λ ↔ z ∈ L.lattice := by
  obtain ⟨w₁, w₂, hi, rfl⟩ := h
  refine ⟨⟨w₁, w₂, hi⟩, fun z => ?_⟩
  rw [PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
  simp only [zsmul_eq_mul]

theorem periodPair_conj (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (h2 : g2 Λ ∈ M) (h3 : g3 Λ ∈ M) :
    ∃ L' : PeriodPair, ∀ z, z ∈ lamConj M ρ Λ ↔ z ∈ L'.lattice := by
  obtain ⟨-, -, hd, -, -, -, hex⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ h
  have hne : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 ≠ 0 := by
    have e : ρ (TaylorLogMetric.liftM M (g2 Λ)) ^ 3 - 27 * ρ (TaylorLogMetric.liftM M (g3 Λ)) ^ 2 =
        ρ (TaylorLogMetric.liftM M (g2 Λ) ^ 3 - 27 * TaylorLogMetric.liftM M (g3 Λ) ^ 2) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
    rw [e, map_ne_zero]
    intro h0
    apply hd
    have := congrArg (fun y : M => (y : ℂ)) h0
    simp only [TaylorLogMetric.liftM, dif_pos h2, dif_pos h3] at this
    exact this
  obtain ⟨L', ha, hb⟩ := hex _ _ hne
  obtain ⟨e2, e3, -, -, -, hun, -⟩ :=
    GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
  have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
    g2 Λ' = ρ (TaylorLogMetric.liftM M (g2 Λ)) ∧ g3 Λ' = ρ (TaylorLogMetric.liftM M (g3 Λ))) ⟨_, e2.trans ha, e3.trans hb⟩
  have : lamConj M ρ Λ = L'.lattice.toAddSubgroup :=
    hun _ (hs.1.trans (e2.trans ha).symm) (hs.2.trans (e3.trans hb).symm)
  exact ⟨L', fun z => by rw [this]; rfl⟩

theorem value_shift_sg (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    (x : ℂ) {l : ℂ} (hl : l ∈ Λ) :
    coef1 (U1 Λ (x + 2 * l) (sgStar Λ)) 0 = ee (gl3FieldFirst Λ x l) * coef1 (U1 Λ x (sgStar Λ)) 0 := by
  simp only [coef1, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  refine value_shift Λ _ x l fun z => ?_
  have h2 : 2 * l ∈ Λ := by rw [two_mul]; exact Λ.add_mem hl hl
  rw [(GlobalTheory.OddTheta.sgStar_laws Λ (isLattice_of_periodPair L Λ h)).1.2.2.2 _ h2 z,
    if_pos (by simpa using hl), one_mul]

theorem value_ne_zero (L : PeriodPair) (Λ : AddSubgroup ℂ) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice)
    {x : ℂ} (hx : x ∉ Λ) : coef1 (U1 Λ x (sgStar Λ)) 0 ≠ 0 := by
  simp only [coef1, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one, U1, zero_add]
  exact mul_ne_zero
    (fun h0 => hx (((GlobalTheory.OddTheta.sgStar_laws Λ (isLattice_of_periodPair L Λ h)).2.1 x).1 h0))
    (Complex.exp_ne_zero _)

theorem natMul_mem {Λ : AddSubgroup ℂ} (n : ℕ) {x : ℂ} (hx : x ∈ Λ) : (n : ℂ) * x ∈ Λ := by
  rw [← nsmul_eq_mul]; exact Λ.nsmul_mem hx n

theorem weil_top (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ)
    (s : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ s) (a b a' b' : ℂ) (m : ℕ) (hm : 0 < m)
    (ha : (m : ℂ) * a ∈ lamOf D cc δ) (hb : (m : ℂ) * b ∈ lamOf D cc δ)
    (haa : Adp1 ⊤ s (lamOf D cc δ) m a a') (hbb : Adp1 ⊤ s (lamOf D cc δ) m b b') :
    cj ⊤ s (ee (gl3FieldFirst (lamOf D cc δ) a b)) = ee (gl3FieldFirst (lamConj ⊤ s (lamOf D cc δ)) a' b') := by
  obtain ⟨L, hL⟩ := periodPair_of_isLattice _
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ hc).1
  obtain ⟨L', hL'⟩ := periodPair_conj L _ hL ⊤ s IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨hex, hun, -, hadd, -, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ hc ⊤ s hK IntermediateField.mem_top IntermediateField.mem_top
  have hgal := GlobalTheory.T.galois_conj_taylor_thetaTranslate D cc δ hc ⊤ s hK IntermediateField.mem_top IntermediateField.mem_top
  generalize lamOf D cc δ = Λ at *
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hmul : ∀ (n : ℕ) t t', StarPt ⊤ s Λ t t' → StarPt ⊤ s Λ (n * t) (n * t') := by
    intro n t t' h
    induction n with
    | zero => exact Or.inl ⟨by simp, by simp⟩
    | succ n ih => simpa [add_mul] using hadd _ _ _ _ ih h
  have ha' : (m : ℂ) * a' ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ haa).1 (by convert ha using 1; push_cast; field_simp)
    convert this using 1; push_cast; field_simp
  have hb' : (m : ℂ) * b' ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ hbb).1 (by convert hb using 1; push_cast; field_simp)
    convert this using 1; push_cast; field_simp
  have e1 : gl3FieldFirst Λ a b = gl3FieldFirst Λ (a / m) (m * b) := by
    rw [latticeRiemannForm_natCast_mul_comm]; congr 1; field_simp
  have e2 : gl3FieldFirst (lamConj ⊤ s Λ) a' b' = gl3FieldFirst (lamConj ⊤ s Λ) (a' / m) (m * b') := by
    rw [latticeRiemannForm_natCast_mul_comm]; congr 1; field_simp
  rw [e1, e2]
  rcases id haa with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [expTwoPiI_latticeRiemannForm_of_mem L Λ hL h1 hb, expTwoPiI_latticeRiemannForm_of_mem L' _ hL' h2 hb', cj_one]
  obtain ⟨t, ht⟩ := hex (a / m / ((2 * (2 * m ^ 2) : ℕ) : ℂ))
    ⟨2 * (2 * m ^ 2) * m ^ 2, by positivity, by convert ha using 1; push_cast; field_simp⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  obtain ⟨u, hu⟩ := hex (b / m / 2)
    ⟨2 * m ^ 2, by positivity, by convert hb using 1; push_cast; field_simp⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have hx : StarPt ⊤ s Λ (a / m) (4 * m ^ 2 * t) := by
    convert hmul (2 * (2 * m ^ 2)) _ _ ht using 1 <;> push_cast <;> field_simp <;> ring
  have hy : StarPt ⊤ s Λ (b / m) (2 * u) := by
    convert hmul 2 _ _ hu using 1 <;> push_cast <;> field_simp
  have hν := (hun _ _ _ hx).1 haa
  have hμ := (hun _ _ _ hy).1 hbb
  have hx' : 4 * m ^ 2 * t ∉ lamConj ⊤ s Λ := by
    rcases hx with h | h
    · exact absurd h.1 h1
    · exact h.2.1
  have hl' : 2 * m ^ 2 * u ∈ lamConj ⊤ s Λ := by
    have := (hord (m ^ 2) _ _ hy).1 (by convert hb using 1; push_cast; field_simp)
    convert this using 1; push_cast; ring
  have g1 := hgal (a / m) (4 * m ^ 2 * t) (2 * m ^ 2) (by positivity)
    (by convert ha using 1; push_cast; field_simp)
    (by unfold Adp1; convert ht using 1; push_cast; field_simp; ring)
    (fun _ => IntermediateField.mem_top) 0
  have g2 := hgal (a / m + 2 * (m * b)) (4 * m ^ 2 * t + 2 * (2 * m ^ 2 * u)) (2 * m ^ 2) (by positivity)
    (by convert Λ.add_mem ha (natMul_mem (2 * m ^ 2) hb) using 1; push_cast; field_simp)
    (by unfold Adp1; convert hadd _ _ _ _ ht hu using 1 <;> push_cast <;> field_simp <;> ring)
    (fun _ => IntermediateField.mem_top) 0
  rw [value_shift_sg L Λ hL _ hb, value_shift_sg L' _ hL' _ hl', cj_top_mul, g1] at g2
  rw [mul_right_cancel₀ (value_ne_zero L' _ hL' hx') g2]
  have e3 : (4 * m ^ 2 * t : ℂ) = a' / m + (4 * m ^ 2 * t - a' / m) := by ring
  have e4 : (2 * m ^ 2 * u : ℂ) = m * b' + m * (m * (2 * u - b' / m)) := by field_simp; ring
  rw [e3, latticeRiemannForm_add_left, ee_add, expTwoPiI_latticeRiemannForm_of_mem L' _ hL' hν hl', mul_one, e4, latticeRiemannForm_add_right, ee_add,
    latticeRiemannForm_natCast_mul_comm _ m _ (m * _), latticeRiemannForm_natCast_mul_comm _ m _ (2 * u - _),
    expTwoPiI_latticeRiemannForm_of_mem L' _ hL' (by convert ha' using 1; field_simp) hμ, mul_one]

theorem weilPairingGalois_all : ∀ D : D7, WeilPairingGaloisAlt D := by
  intro D cc δ hc M ρ hK h2 h3 a b a' b' m hm ha hb haa hbb he
  set Λ := lamOf D cc δ with hΛ
  let S : Set ℂ := (Set.range (fun k : D.host.K => D.host.φ₀ (k : D.host.E)) ∪
    {g2 Λ, g3 Λ, ee (gl3FieldFirst Λ a b), wpF Λ (a / m), wpD Λ (a / m), wpF Λ (b / m), wpD Λ (b / m)}) ∩ M
  haveI : Countable D.host.K := by
    haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
    infer_instance
  have hS : S.Countable :=
    ((Set.countable_range _).union (Set.toFinite _).countable).mono Set.inter_subset_left
  obtain ⟨s, hs⟩ := exists_top_agree M ρ S hS fun x hx => hx.2
  have hlam : lamConj ⊤ s Λ = lamConj M ρ Λ := by
    have e2 := hs (g2 Λ) ⟨Or.inr (by simp), h2⟩
    have e3 := hs (g3 Λ) ⟨Or.inr (by simp), h3⟩
    unfold cj at e2 e3
    unfold lamConj
    rw [e2, e3]
  have hK' : FixK D ⊤ s := fun k =>
    ⟨IntermediateField.mem_top, (hs _ ⟨Or.inl ⟨k, rfl⟩, (hK k).1⟩).trans (hK k).2⟩
  have hst : ∀ t t', (t = a / m ∨ t = b / m) → StarPt M ρ Λ t t' → StarPt ⊤ s Λ t t' := by
    intro t t' ht h
    unfold StarPt
    rw [hlam]
    rcases h with h | ⟨h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · refine Or.inr ⟨h1, h2, IntermediateField.mem_top, IntermediateField.mem_top, ?_, ?_⟩
      · rw [h5, hs _ ⟨Or.inr (by rcases ht with rfl | rfl <;> simp), h3⟩]
      · rw [h6, hs _ ⟨Or.inr (by rcases ht with rfl | rfl <;> simp), h4⟩]
  rw [← hs _ ⟨Or.inr (by simp), he⟩, ← hlam]
  exact weil_top D cc δ hc s hK' a b a' b' m hm ha hb (hst _ _ (Or.inl rfl) haa)
    (hst _ _ (Or.inr rfl) hbb)

end GlobalTheory.WeilPairingGalois
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsionStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion : ∀ D : D7, WeilPairingGaloisAlt D := by
  first | exact @GlobalTheory.WeilPairingGalois.weilPairingGalois_all | exact GlobalTheory.WeilPairingGalois.weilPairingGalois_all | (intros; apply GlobalTheory.WeilPairingGalois.weilPairingGalois_all <;> assumption)
end
end
