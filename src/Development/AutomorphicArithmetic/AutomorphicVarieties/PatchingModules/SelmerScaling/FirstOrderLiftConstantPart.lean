module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.FirstOrderMatrixMemSquareZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlSel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.ConjConst

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InvEv
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.invEv :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), l ≠ 2 → ∀ Y : Matrix (Fin n) (Fin n) x.Fr, Y ∈ Ev x.A x.Fr n x.a → Yᵀ = -Y → (∀ g : G.G₀, dY G.frame (fun g => x.ρX x.Fr (h.p₀ g)) Y g = 0) → Y = 0 := by
  intro l hl L G G0 h n x hl2 Y _ hT hd
  have hmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := by
    intro g g'
    simp only [NP.ρX, mat, map_mul, Units.val_mul]
    exact Matrix.map_mul
  have hone : x.ρX x.Fr 1 = 1 := by
    simp only [NP.ρX, mat, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hsurj : Function.Surjective h.p₀ := by
    intro g
    obtain ⟨γ, hγ⟩ := h.surj g.1
    have hm : γ ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, ← h.η γ, hγ]
      exact g.2
    exact ⟨⟨γ, hm⟩, Subtype.ext hγ⟩
  have hc : ∀ g, x.ρX x.Fr g * Y = Y * x.ρX x.Fr g := by
    intro g
    obtain ⟨γ, rfl⟩ := hsurj g
    have e := hd γ
    simp only [dY, sub_eq_zero] at e
    have e2 : x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := by
      rw [← hmul, ← map_mul, inv_mul_cancel, map_one, hone]
    calc x.ρX x.Fr (h.p₀ γ) * Y
        = x.ρX x.Fr (h.p₀ γ) * Y * (x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ)) := by rw [e2, mul_one]
      _ = Y * x.ρX x.Fr (h.p₀ γ) := by rw [← mul_assoc, e]
  have hs : ∀ Z ∈ Submodule.span x.A (mat x.ρ '' (G0.frame.G' : Set G0.frame.G₀)),
      Z.map (algebraMap x.A x.Fr) * Y = Y * Z.map (algebraMap x.A x.Fr) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, _, rfl⟩ := hZ
      exact hc g
    | zero => simp
    | add a b _ _ ha hb =>
      rw [Matrix.map_add _ (map_add _), add_mul, mul_add, ha, hb]
    | smul c a _ ha =>
      have : (c • a).map (algebraMap x.A x.Fr) = algebraMap x.A x.Fr c • a.map (algebraMap x.A x.Fr) := by
        ext i j; simp
      rw [this, Matrix.smul_mul, Matrix.mul_smul, ha]
  have h2 : (2 : x.Fr) ≠ 0 := by
    have hu : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      have : ¬ ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by
        rw [PadicInt.norm_int_lt_one_iff_dvd]
        intro hdv
        have : l ∣ 2 := by exact_mod_cast hdv
        exact hl2 ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 this)
      have h3 : ‖((2 : ℤ) : ℤ_[l])‖ = 1 := le_antisymm (PadicInt.norm_le_one _) (not_lt.1 this)
      simpa using h3
    have := (hu.map (((algebraMap x.A x.Fr).comp (algebraMap x.K x.A)).comp (algebraMap ℤ_[l] x.K))).ne_zero
    rwa [map_ofNat] at this
  ext i j
  by_cases hij : i = j
  · subst hij
    have e := congrFun (congrFun hT i) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at e
    have : (2 : x.Fr) * Y i i = 0 := by linear_combination e
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · have hE : (Matrix.single i i (1 : x.A)) ∈ Ev x.A x.A n x.a := by
      intro p q
      refine ⟨fun _ => trivial, fun hne => ?_⟩
      rw [Submodule.mem_bot]
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact hne Iff.rfl
    obtain ⟨s, hsp⟩ := x.span _ hE
    have e := hs _ hsp
    have hm : ((PowerSeries.X : PowerSeries x.K) ^ s • Matrix.single i i (1 : x.A)).map (algebraMap x.A x.Fr)
        = Matrix.single i i (algebraMap x.A x.Fr (x.t ^ s)) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.map_single]
    rw [hm] at e
    have e' := congrFun (congrFun e i) j
    rw [Matrix.single_mul_apply_same, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm hij)] at e'
    have ht : algebraMap x.A x.Fr (x.t ^ s) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact pow_ne_zero _ PowerSeries.X_ne_zero
    simpa using (mul_eq_zero.1 e').resolve_left ht
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EOneTranspose
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}

private theorem alg_eq (c : A) : algebraMap A (DD X g) c = DD.C (algebraMap A X c) := rfl

end SlopeTestRemainingChoices

section Conj

variable {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X]

end Conj

end UpperTheory.V.Pa

private theorem dd_ep_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ c ∈ s, f c).ep m = ∑ c ∈ s, (f c).ep m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_ep, ih]

private theorem ep_component_add {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ c ∈ s, f c).a = ∑ c ∈ s, (f c).a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_a, ih]

private theorem dd_ep'_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ c ∈ s, f c).ep' m = ∑ c ∈ s, (f c).ep' m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_ep']
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_ep', ih]

private theorem dd_eta_finset_sum {X : Type} [CommRing X] {g : ℕ} {ι : Type} (s : Finset ι) (f : ι → DD X g) :
    (∑ c ∈ s, f c).eta = ∑ c ∈ s, (f c).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_eta]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DD.add_eta, ih]

private theorem epM_mul_epM_eq_zero {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM f * DD.epM f' = 0 := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM, DD.zero_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.zero_ep]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.zero_ep']
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.zero_eta]

private theorem map_C_mul_epM {X : Type} [CommRing X] {g n : ℕ} (P : Matrix (Fin n) (Fin n) X) (f : Fin g → Matrix (Fin n) (Fin n) X) :
    P.map DD.C * DD.epM f = DD.epM (fun m => P * f m) := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.C_ep, DD.C_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.C_ep', DD.C_a]
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.C_eta, DD.C_ep, DD.C_ep']

private theorem epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P : Matrix (Fin n) (Fin n) X) (f : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM f * P.map DD.C = DD.epM (fun m => f m * P) := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [Matrix.mul_apply, ep_component_add, DD.mul_a, DD.epM]
  · funext m
    simp [Matrix.mul_apply, dd_ep_finset_sum, DD.mul_ep, DD.epM, DD.C_ep, DD.C_a]
  · funext m
    simp [Matrix.mul_apply, dd_ep'_finset_sum, DD.mul_ep', DD.epM, DD.C_ep', DD.C_a]
  · simp [Matrix.mul_apply, dd_eta_finset_sum, DD.mul_eta, DD.epM, DD.C_eta, DD.C_ep, DD.C_ep']

private theorem epM_pi_add {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (f + f') = DD.epM f + DD.epM f' := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.add_a, DD.epM]
  · funext m
    simp [DD.add_ep, DD.epM]
  · funext m
    simp [DD.add_ep', DD.epM]
  · simp [DD.add_eta, DD.epM]

private theorem epM_pi_zero {X : Type} [CommRing X] {g n : ℕ} :
    DD.epM (0 : Fin g → Matrix (Fin n) (Fin n) X) = 0 := by
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.zero_a, DD.epM]
  · funext m
    simp [DD.zero_ep, DD.epM]
  · funext m
    simp [DD.zero_ep', DD.epM]
  · simp [DD.zero_eta, DD.epM]

private theorem epM_neg_transpose {X : Type} [CommRing X] {g n : ℕ} (f : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (fun m => -(f m)ᵀ) = -(DD.epM f)ᵀ := by
  have hn : ∀ y : DD X g, -y = 0 - y := fun y => (zero_sub y).symm
  refine Matrix.ext fun a b => DD.ext ?_ ?_ ?_ ?_
  · simp [DD.neg_a, DD.epM]
  · funext m
    simp [DD.neg_ep, DD.epM]
  · funext m
    have h1 := DD.add_ep' (-(DD.epM f b a)) (DD.epM f b a) m
    rw [neg_add_cancel, DD.zero_ep'] at h1
    simp [DD.epM] at h1 ⊢
  · have h1 := DD.add_eta (-(DD.epM f b a)) (DD.epM f b a)
    rw [neg_add_cancel, DD.zero_eta] at h1
    simp [DD.epM] at h1 ⊢

private theorem one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P P' : Matrix (Fin n) (Fin n) X) (f u u' : Fin g → Matrix (Fin n) (Fin n) X) :
    (1 + DD.epM u) * P.map DD.C * DD.epM f * ((1 + DD.epM u') * P'.map DD.C) = DD.epM (fun m => P * f m * P') := by
  rw [mul_assoc (1 + DD.epM u), map_C_mul_epM, add_mul, one_mul, epM_mul_epM_eq_zero, add_zero, ← mul_assoc,
    mul_add, mul_one, epM_mul_epM_eq_zero, add_zero, epM_mul_map_C]

private theorem map_C_mul_one_add_epM_mul_epM_mul_one_sub_epM_mul_map_C {X : Type} [CommRing X] {g n : ℕ} (P P' : Matrix (Fin n) (Fin n) X) (f u u' : Fin g → Matrix (Fin n) (Fin n) X) :
    P.map DD.C * (1 + DD.epM u) * DD.epM f * ((1 - DD.epM u') * P'.map DD.C) = DD.epM (fun m => P * f m * P') := by
  rw [mul_assoc (P.map DD.C), add_mul, one_mul, epM_mul_epM_eq_zero, add_zero, map_C_mul_epM, ← mul_assoc,
    mul_sub, mul_one, epM_mul_epM_eq_zero, sub_zero, epM_mul_map_C]

private theorem epM_single_map_mem_W1_of_mem_Od {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n : ℕ} (g a : ℕ) (j : Fin g)
    (M : Matrix (Fin n) (Fin n) A) (hM : M ∈ Od A A n a) :
    DD.epM (Pi.single j (M.map (algebraMap A X))) ∈ W1 n A X g a := by
  unfold W1 blkMat ddPart
  unfold Od at hM
  intro r c
  have hrc := hM r c
  refine ⟨fun hd => ?_, fun _ => ?_⟩
  · have h0 : M r c = 0 := by simpa using hrc.1 hd
    refine ⟨fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
    · funext m
      by_cases hm : m = j
      · subst hm
        simp [DD.epM, h0]
      · simp [DD.epM, Pi.single_apply, hm]
    · funext m
      simp [DD.epM]
    · simp [DD.epM]
  · refine ⟨fun _ => ?_, fun h => absurd h (by decide), fun _ => ?_, fun _ => ?_⟩
    · simp [DD.epM]
    · funext m
      simp [DD.epM]
    · simp [DD.epM]

private theorem adicCont_const_fun {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) (c : R) :
    AdicCont I (fun _ : Γ => c) := by
  unfold AdicCont
  intro N
  exact IsLocallyConstant.const _

private theorem adicCont_epM_single_map_apply {Γ A X : Type} [TopologicalSpace Γ] [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (t : A) (j : Fin g) (F : Γ → Matrix (Fin n) (Fin n) A) (a b : Fin n)
    (hf : AdicCont (Ideal.span {t}) fun γ => F γ a b) :
    AdicCont (Ideal.span {algebraMap A (DD X g) t}) fun γ => DD.epM (Pi.single j ((F γ).map (algebraMap A X))) a b := by
  set ε : DD X g := DD.epM (Pi.single j (Matrix.of fun _ _ => (1 : X))) a b with hε
  have he : ∀ c : A, ∀ M : Matrix (Fin n) (Fin n) A, M a b = c →
      DD.epM (Pi.single j (M.map (algebraMap A X))) a b = algebraMap A (DD X g) c * ε := by
    intro c M hc
    rw [alg_eq]
    refine DD.ext ?_ ?_ ?_ ?_
    · simp [hε, DD.epM, DD.mul_a, DD.C_a]
    · funext m
      by_cases hm : m = j
      · subst hm
        simp [hε, DD.epM, DD.mul_ep, DD.C_a, DD.C_ep, hc]
      · simp [hε, DD.epM, DD.mul_ep, DD.C_a, DD.C_ep, Pi.single_apply, hm]
    · funext m
      simp [hε, DD.epM, DD.mul_ep', DD.C_a, DD.C_ep']
    · simp [hε, DD.epM, DD.mul_eta, DD.C_eta, DD.C_ep, DD.C_ep']
  unfold AdicCont at hf ⊢
  intro N
  refine (IsLocallyConstant.iff_exists_open _).2 fun γ => ?_
  obtain ⟨U, hU, hγ, hUe⟩ := (IsLocallyConstant.iff_exists_open _).1 (hf N) γ
  refine ⟨U, hU, hγ, fun γ' hγ' => ?_⟩
  have h1 := hUe γ' hγ'
  rw [Ideal.Quotient.eq] at h1 ⊢
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h1
  obtain ⟨d, hd⟩ := h1
  beta_reduce at hd ⊢
  rw [he _ (F γ') rfl, he _ (F γ) rfl, ← sub_mul, ← map_sub, hd, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨algebraMap A (DD X g) d * ε, by rw [map_mul, map_pow, mul_assoc]⟩

private theorem bndD_epM_single_map_of_adicCont {Γ A X : Type} [TopologicalSpace Γ] [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ}
    (t : A) (j : Fin g) (F : Γ → Matrix (Fin n) (Fin n) A)
    (hf : ∀ a b : Fin n, AdicCont (Ideal.span {t}) fun γ => F γ a b) :
    BndD t fun γ => DD.epM (Pi.single j ((F γ).map (algebraMap A X))) := by
  have hz : BndF t (fun _ : Γ => (0 : X)) :=
    ⟨0, fun _ => 0, adicCont_const_fun _ _, fun _ => by simp⟩
  unfold BndD
  intro a b
  refine ⟨?_, fun m => ?_, fun m => ?_, ?_⟩
  · simpa [DD.epM] using hz
  · by_cases hm : m = j
    · subst hm
      refine ⟨0, fun γ => F γ a b, hf a b, fun γ => ?_⟩
      simp [DD.epM]
    · simpa [DD.epM, Pi.single_apply, hm] using hz
  · simpa [DD.epM] using hz
  · simpa [DD.epM] using hz

private theorem epM_pi_sub {X : Type} [CommRing X] {g n : ℕ} (f f' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM (f - f') = DD.epM f - DD.epM f' := by
  rw [eq_sub_iff_add_eq, ← epM_pi_add, sub_add_cancel]

private theorem epM_single_map_apply_eq_zero_of_apply_eq_zero {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n : ℕ} (j : Fin g)
    (M : Matrix (Fin n) (Fin n) A) (r c : Fin n) (hM : M r c = 0) :
    DD.epM (Pi.single j (M.map (algebraMap A X))) r c = 0 := by
  refine DD.ext ?_ ?_ ?_ ?_
  · simp [DD.epM, DD.zero_a]
  · funext m
    by_cases hm : m = j
    · subst hm
      simp [DD.epM, DD.zero_ep, hM]
    · simp [DD.epM, DD.zero_ep, Pi.single_apply, hm]
  · funext m
    simp [DD.epM, DD.zero_ep']
  · simp [DD.epM, DD.zero_eta]

theorem UpperTheory.V.Pa.kapSel1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ i j : Fin k.g, (fun γ => DD.epM (Pi.single j (kapF h k i γ))) ∈ Sel1 h x.Fr k ∧ BndD x.t fun γ => DD.epM (Pi.single j (kapF h k i γ)) := by
  intro l _ L G G0 h n x k i j
  have hm := k.mem i
  simp only [SelZ, Set.mem_setOf_eq] at hm
  obtain ⟨hOd, hcont, hcoc, hconj, hIu, hloc⟩ := hm
  have hpc : Continuous h.p₀ := Continuous.codRestrict (h.cont.comp continuous_subtype_val) _
  have hc' : ∀ a b : Fin n, AdicCont (Ideal.span {x.t}) fun γ : G.frame.G₀ => k.κ i (h.p₀ γ) a b := by
    intro a b
    have h1 := hcont a b
    rw [Algebra.algebraMap_self, RingHom.id_apply] at h1
    unfold AdicCont at h1 ⊢
    intro N
    exact (h1 N).comp_continuous hpc
  refine ⟨?_, bndD_epM_single_map_of_adicCont x.t j (fun γ => k.κ i (h.p₀ γ)) hc'⟩
  simp only [Sel1, SelZ, Set.mem_setOf_eq]
  refine ⟨fun γ => epM_single_map_mem_W1_of_mem_Od _ _ j _ (hOd _), fun a b => adicCont_epM_single_map_apply x.t j _ a b (hc' a b), fun g g' => ?_,
    fun g => ?_, fun u g hg => ?_, fun v => ?_⟩
  · show DD.epM (Pi.single j ((k.κ i (h.p₀ (g * g'))).map (algebraMap x.A x.Fr))) =
      DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))) +
        k.ρ1 x.Fr (h.p₀ g) * DD.epM (Pi.single j ((k.κ i (h.p₀ g')).map (algebraMap x.A x.Fr))) *
          k.ρ1 x.Fr (h.p₀ g⁻¹)
    rw [map_mul, hcoc, Matrix.map_add _ (map_add _), Pi.single_add, epM_pi_add]
    congr 1
    unfold Kap.ρ1
    rw [show x.ρX (DD x.Fr k.g) (h.p₀ g) = (x.ρX x.Fr (h.p₀ g)).map DD.C from rfl,
      show x.ρX (DD x.Fr k.g) (h.p₀ g⁻¹) = (x.ρX x.Fr (h.p₀ g⁻¹)).map DD.C from rfl, one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C]
    congr 1
    funext m
    by_cases hmj : m = j
    · subst hmj
      simp only [Pi.single_eq_same, map_inv, Matrix.map_mul]
      rfl
    · simp [Pi.single_apply, hmj]
  · have hcj : h.p₀ (G.frame.conj g) = G0.frame.conj (h.p₀ g) := by
      apply Subtype.ext
      simp [Glob.Hom.p₀, Glob.frame, GFrame.conj, h.c]
    show DD.epM (Pi.single j ((k.κ i (h.p₀ (G.frame.conj g))).map (algebraMap x.A x.Fr))) =
      -(DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))))ᵀ
    rw [hcj, hconj, ← epM_neg_transpose]
    congr 1
    funext m
    by_cases hmj : m = j
    · subst hmj
      rw [Pi.single_eq_same, Pi.single_eq_same, Matrix.map_neg _ (map_neg _), Matrix.transpose_map]
    · simp [Pi.single_apply, hmj]
  · have hg' : h.p₀ g ∈ Subgroup.map (G0.φu u) (L.Ju u) := by
      obtain ⟨a, ha, rfl⟩ := hg
      refine ⟨a, ha, ?_⟩
      apply Subtype.ext
      simp [Glob.Hom.p₀, h.φu]
    show DD.epM (Pi.single j ((k.κ i (h.p₀ g)).map (algebraMap x.A x.Fr))) = 0
    rw [hIu u _ hg', Matrix.map_zero _ (map_zero _), Pi.single_zero, epM_pi_zero]
  · obtain ⟨Y, hY, hLY⟩ := hloc v
    refine ⟨DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))), epM_single_map_mem_W1_of_mem_Od _ _ j _ hY, ?_⟩
    unfold LocAt at hLY ⊢
    intro gv
    obtain ⟨h1, h2⟩ := hLY gv
    have hφ : h.p₀ ((G.frame.φ v) gv) = (G0.frame.φ v) gv := by
      apply Subtype.ext
      simp [Glob.Hom.p₀, Glob.frame, h.φ]
    have key : k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v =
        DD.epM (Pi.single j ((x.wiX x.A v * (k.κ i ((G0.frame.φ v) gv) - dY G0.frame (x.ρX x.A) Y ((G0.frame.φ v) gv)) *
          x.wX x.A v).map (algebraMap x.A x.Fr))) := by
      unfold dY Kap.ρ1 Kap.wi1 Kap.w1
      beta_reduce
      rw [map_inv, hφ,
        show x.ρX (DD x.Fr k.g) ((G0.frame.φ v) gv) = (x.ρX x.Fr ((G0.frame.φ v) gv)).map DD.C from rfl,
        show x.ρX (DD x.Fr k.g) ((G0.frame.φ v) gv)⁻¹ = (x.ρX x.Fr ((G0.frame.φ v) gv)⁻¹).map DD.C from rfl,
        show x.wiX (DD x.Fr k.g) v = (x.wiX x.Fr v).map DD.C from rfl,
        show x.wX (DD x.Fr k.g) v = (x.wX x.Fr v).map DD.C from rfl,
        one_add_epM_mul_map_C_mul_epM_mul_one_add_epM_mul_map_C, ← epM_pi_sub, ← epM_pi_sub, map_C_mul_one_add_epM_mul_epM_mul_one_sub_epM_mul_map_C]
      congr 1
      funext m
      by_cases hmj : m = j
      · subst hmj
        simp only [Pi.sub_apply, Pi.single_eq_same, Matrix.map_mul, Matrix.map_sub _ (map_sub (algebraMap x.A x.Fr))]
        rfl
      · simp [Pi.single_apply, hmj]
    refine ⟨fun r c hrc => ?_, fun hmu r => ?_⟩
    · show (k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v) r c = 0
      rw [key]
      exact epM_single_map_apply_eq_zero_of_apply_eq_zero j _ r c (h1 r c hrc)
    · show (k.wi1 x.Fr v * (DD.epM (Pi.single j ((k.κ i (h.p₀ ((G.frame.φ v) gv))).map (algebraMap x.A x.Fr))) -
        dY G.frame (fun g => k.ρ1 x.Fr (h.p₀ g)) (DD.epM (Pi.single j (Y.map (algebraMap x.A x.Fr))))
          ((G.frame.φ v) gv)) * k.w1 x.Fr v) r r = 0
      rw [key]
      exact epM_single_map_apply_eq_zero_of_apply_eq_zero j _ r r (h2 hmu r)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {X : Type} [CommRing X] {g n : ℕ}

private def aH (X : Type) [CommRing X] (g : ℕ) : DD X g →+ X where
  toFun u := u.a
  map_zero' := rfl
  map_add' _ _ := rfl

private def epH (X : Type) [CommRing X] {g : ℕ} (j : Fin g) : DD X g →+ X where
  toFun u := u.ep j
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (aH X g) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (m : Fin g) :
    (∑ i ∈ s, f i).ep m = ∑ i ∈ s, (f i).ep m :=
  map_sum (epH X m) f s

private theorem sub_a (u v : DD X g) : (u - v).a = u.a - v.a := by
  rfl

private theorem sub_ep (u v : DD X g) (m : Fin g) : (u - v).ep m = u.ep m - v.ep m := by
  rfl

private theorem smul_a (c : X) (u : DD X g) : (c • u).a = c * u.a := rfl

private theorem smul_ep (c : X) (u : DD X g) (m : Fin g) : (c • u).ep m = c * u.ep m := by
  rw [Algebra.smul_def]
  show _ = _
  simp [DD.instAlgebra]
  rw [RingHom.algebraMap_toAlgebra]
  simp [DD.C]
  change c * u.ep m + (0 : Fin g → X) m * u.a = c * u.ep m
  simp

private theorem mul_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P * Q).map (fun u => u.a) = P.map (fun u => u.a) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, sum_a]
  rfl

private theorem mul_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P * Q).map (fun u => u.ep m) =
      P.map (fun u => u.a) * Q.map (fun u => u.ep m) + P.map (fun u => u.ep m) * Q.map (fun u => u.a) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, sum_ep, ← Finset.sum_add_distrib]
  rfl

private theorem sub_mapa (P Q : Matrix (Fin n) (Fin n) (DD X g)) :
    (P - Q).map (fun u => u.a) = P.map (fun u => u.a) - Q.map (fun u => u.a) := by
  ext a b
  simp [sub_a]

private theorem sub_mapep (P Q : Matrix (Fin n) (Fin n) (DD X g)) (m : Fin g) :
    (P - Q).map (fun u => u.ep m) = P.map (fun u => u.ep m) - Q.map (fun u => u.ep m) := by
  ext a b
  simp [sub_ep]

end SlopeTestRemainingChoices

private theorem first_order_lift_constant_part {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type) [CommRing X]
    [Algebra x.A X] (γ : F.G₀) : (k.ρ1 X γ).map (fun u => u.a) = x.ρX X γ := by
  unfold Kap.ρ1
  rw [mul_mapa]
  have h1 : (1 + DD.epM fun j => (k.κ j γ).map (algebraMap x.A X)).map (fun u : DD X k.g => u.a) =
      (1 : Matrix (Fin n) (Fin n) X) := by
    ext i j
    rw [Matrix.map_apply, Matrix.add_apply]
    change ((1 : Matrix (Fin n) (Fin n) (DD X k.g)) i j).a + 0 = (1 : Matrix (Fin n) (Fin n) X) i j
    rw [add_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · rfl
    · rfl
  have h2 : (x.ρX (DD X k.g) γ).map (fun u => u.a) = x.ρX X γ := by
    ext i j
    rfl
  rw [h1, h2, one_mul]

end UpperTheory.V.Pa

private theorem card_le_of_linearIndependent_mod_bd1_in_sel1 {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ}
    {x : NP G0.frame n} (k : Kap x) (D0 : ℕ) (hK : SelmerRankBoundLaurent h k D0) {ι : Type} [Fintype ι]
    (z : ι → G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g))
    (hz : ∀ i, z i ∈ Sel1 h x.Fr k ∧ BndD x.t (z i))
    (hind : ∀ c : ι → x.Fr, ∑ i, c i • z i ∈ Bd1 h x.Fr k → c = 0) : Fintype.card ι ≤ D0 := by
  let q := Fintype.equivFin ι
  refine hK _ (fun j => z (q.symm j)) (fun j => hz _) ?_
  intro c hc
  have h0 : (fun i => c (q i)) = 0 := by
    apply hind
    have hs : ∑ i, c (q i) • z i = ∑ j, c j • z (q.symm j) := by
      rw [← Equiv.sum_comp q (fun j => c j • z (q.symm j))]
      simp
    rw [hs]
    exact hc
  funext j
  have := congrFun h0 (q.symm j)
  simpa using this

private theorem map_a_rho1_mul_mul_sub_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.a) =
      x.ρX X γ * Y.map (fun u => u.a) * x.ρX X δ - Y.map (fun u => u.a) := by
  rw [sub_mapa, mul_mapa, mul_mapa, first_order_lift_constant_part, first_order_lift_constant_part]

private theorem map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (γ δ : F.G₀) (Y : Matrix (Fin n) (Fin n) (DD X k.g)) (m : Fin k.g)
    (hY : Y.map (fun u => u.a) = 0) :
    (k.ρ1 X γ * Y * k.ρ1 X δ - Y).map (fun u => u.ep m) =
      x.ρX X γ * Y.map (fun u => u.ep m) * x.ρX X δ - Y.map (fun u => u.ep m) := by
  rw [sub_mapep, mul_mapep, mul_mapep, mul_mapa, hY, first_order_lift_constant_part, first_order_lift_constant_part]
  simp

private theorem dd_a_add_of_commRing {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) : (u + v).a = u.a + v.a := rfl

private theorem dd_ep_add_apply {X : Type} [CommRing X] {g : ℕ} (u v : DD X g) (m : Fin g) :
    (u + v).ep m = u.ep m + v.ep m := rfl

theorem UpperTheory.V.Pa.claim1 :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ D0, SelmerRankBoundLaurent S.h S.k D0 → ∀ (e : ℕ) (α : Fin e → S.Tp), LinearIndependent S.F α → (∀ i j, Lifts S.h S.k (Pi.single j (S.alC (α i)))) → e + S.k.g * S.k.g ≤ D0 := by
  intro l _ S D0 hK e α hα hl
  classical
  have hsel : ∀ i, S.alC (α i) ∈ SelP S.h S.x S.F ∧ BndM S.x.t (S.alC (α i)) :=
    fun i => (alSel l S).1 _ (α i).2
  choose y hy1 hy2 hy3 using fun i => lift1 l S.L S.G S.G0 S.h S.n S.x S.k _ (hsel i).1 (hsel i).2 (hl i)
  have hy4 : ∀ i γ a b, (y i γ a b).a = S.alC (α i) γ a b := by
    intro i γ a b
    rw [← hy3]
    rfl
  let w : Fin S.k.g × Fin S.k.g → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    fun p γ => DD.epM (Pi.single p.2 (kapF S.h S.k p.1 γ))
  have hw0 : ∀ p γ a b, (w p γ a b).a = 0 := fun _ _ _ _ => rfl
  let z : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.G.G₀ → Matrix (Fin S.n) (Fin S.n) (DD S.x.Fr S.k.g) :=
    Sum.elim y w
  have hz : ∀ i, z i ∈ Sel1 S.h S.x.Fr S.k ∧ BndD S.x.t (z i) := by
    rintro (i | p)
    · exact ⟨hy1 i, hy2 i⟩
    · exact kapSel1 l S.L S.G S.G0 S.h S.n S.x S.k p.1 p.2
  have hind : ∀ c : Fin e ⊕ (Fin S.k.g × Fin S.k.g) → S.x.Fr,
      ∑ i, c i • z i ∈ Bd1 S.h S.x.Fr S.k → c = 0 := by
    intro c hc
    obtain ⟨Y, hYW, hYt, hYeq⟩ := hc
    have hsum : ∑ i, c i • z i = ∑ i, c (Sum.inl i) • y i + ∑ p, c (Sum.inr p) • w p := by
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsum] at hYeq
    have hA : ∀ γ, (∑ i, c (Sum.inl i) • S.alC (α i)) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.a) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.a) := by
      intro γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.a)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_a_rho1_mul_mul_sub_eq] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_a_add_of_commRing, sum_a, smul_a, hy4, hw0, smul_eq_mul, mul_zero,
        Finset.sum_const_zero, add_zero]
    have hnegA : ∀ u : DD S.x.Fr S.k.g, (-u).a = -u.a := fun u => map_neg (aH S.x.Fr S.k.g) u
    have hTA : (Y.map (fun u => u.a))ᵀ = -(Y.map (fun u => u.a)) := by
      rw [← Matrix.transpose_map, hYt]
      ext a b
      simp only [Matrix.map_apply, Matrix.neg_apply, hnegA]
    have hEv : Y.map (fun u => u.a) ∈ Ev S.x.A S.x.Fr S.n S.x.a := by
      intro a b
      refine ⟨fun _ => Submodule.mem_top, fun hab => ?_⟩
      have h1 := ((hYW a b).2 hab).1 rfl
      exact (Submodule.mem_bot _).2 h1
    have hmem : ∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F) ∈ S.Tp :=
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (α i).2)
    have hBd : S.alC (∑ i, c (Sum.inl i) • (α i : S.Bh →+ S.F)) ∈ BdP S.h S.x S.F := by
      rw [(alSel l S).2.2.1 (Fin e) (fun i => c (Sum.inl i)) (fun i => (α i : S.Bh →+ S.F))]
      refine ⟨Y.map (fun u => u.a), hEv, hTA, ?_⟩
      funext γ
      exact hA γ
    have hz0 := alInj l S _ hmem hBd
    have hc1 : ∀ i, c (Sum.inl i) = 0 := by
      refine Fintype.linearIndependent_iff.1 hα (fun i => c (Sum.inl i)) ?_
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simpa using hz0
    have hYa : Y.map (fun u => u.a) = 0 := by
      refine invEv l S.L S.G S.G0 S.h S.n S.x S.odd _ hEv hTA ?_
      intro γ
      simp only [dY]
      rw [← hA γ]
      simp [hc1]
    have hEp : ∀ m : Fin S.k.g, ∀ γ, (∑ i, c (Sum.inr (i, m)) • kapF S.h S.k i) γ =
        S.x.ρX S.x.Fr (S.h.p₀ γ) * Y.map (fun u => u.ep m) * S.x.ρX S.x.Fr (S.h.p₀ γ⁻¹) -
          Y.map (fun u => u.ep m) := by
      intro m γ
      have e1 := congrArg (fun M => M.map (fun u : DD S.x.Fr S.k.g => u.ep m)) (congrFun hYeq γ)
      simp only [dY] at e1
      rw [map_ep_rho1_mul_mul_sub_eq_of_map_a_eq_zero _ _ _ _ _ _ hYa] at e1
      rw [← e1]
      ext a b
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Matrix.map_apply, Matrix.add_apply,
        Matrix.sum_apply, Matrix.smul_apply, dd_ep_add_apply, sum_ep, smul_ep, hc1, zero_mul,
        Finset.sum_const_zero, zero_add, smul_eq_mul]
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hw : ∀ j, (w (i, j) γ a b).ep m = if m = j then kapF S.h S.k i γ a b else 0 := by
        intro j
        show (Pi.single j (kapF S.h S.k i γ) : Fin S.k.g → _) m a b = _
        rw [Pi.single_apply]
        split_ifs
        · rfl
        · rfl
      simp only [hw, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hd : ∀ m, (fun i => c (Sum.inr (i, m))) = 0 := by
      intro m
      have hnegE : ∀ u : DD S.x.Fr S.k.g, (-u).ep m = -u.ep m := fun u => map_neg (epH S.x.Fr m) u
      apply indF l S.L S.G S.G0 S.h S.n S.x S.k
      refine ⟨Y.map (fun u => u.ep m), ?_, ?_, ?_⟩
      · intro a b
        refine ⟨fun hab => ?_, fun _ => Submodule.mem_top⟩
        have h1 := ((hYW a b).1 hab).2.1 rfl
        exact (Submodule.mem_bot _).2 (congrFun h1 m)
      · rw [← Matrix.transpose_map, hYt]
        ext a b
        simp only [Matrix.map_apply, Matrix.neg_apply, hnegE]
      · funext γ
        exact hEp m γ
    funext s
    rcases s with i | p
    · exact hc1 i
    · exact congrFun (hd p.2) p.1
  have := card_le_of_linearIndependent_mod_bd1_in_sel1 S.h S.k D0 hK z hz hind
  simpa using this
