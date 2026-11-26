module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.FrameMemLocP
noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem osmul (o : 𝓞 E) (v : S.V) : o • v = (o : E) • v :=
  (algebraMap_smul E o v).symm

theorem one_nmem (p : Ideal (𝓞 E)) [hp : p.IsPrime] : (1 : 𝓞 E) ∉ p :=
  (Ideal.ne_top_iff_one p).mp hp.ne_top

def locInt (p : Ideal (𝓞 E)) [hp : p.IsPrime] : Subring E where
  carrier := {c | ∃ s : 𝓞 E, s ∉ p ∧ ∃ a : 𝓞 E, (s : E) * c = a}
  mul_mem' := by
    rintro c₁ c₂ ⟨s₁, hs₁, a₁, h₁⟩ ⟨s₂, hs₂, a₂, h₂⟩
    refine ⟨s₁ * s₂, fun h => (hp.mem_or_mem h).elim hs₁ hs₂, a₁ * a₂, ?_⟩
    push_cast
    linear_combination ((s₂ : E) * c₂) * h₁ + (a₁ : E) * h₂
  one_mem' := ⟨1, one_nmem p, 1, by simp⟩
  add_mem' := by
    rintro c₁ c₂ ⟨s₁, hs₁, a₁, h₁⟩ ⟨s₂, hs₂, a₂, h₂⟩
    refine ⟨s₁ * s₂, fun h => (hp.mem_or_mem h).elim hs₁ hs₂, a₁ * s₂ + s₁ * a₂, ?_⟩
    push_cast
    linear_combination (s₂ : E) * h₁ + (s₁ : E) * h₂
  zero_mem' := ⟨1, one_nmem p, 0, by simp⟩
  neg_mem' := by
    rintro c ⟨s, hs, a, h⟩
    exact ⟨s, hs, -a, by push_cast; linear_combination -h⟩

theorem coe_mem_locInt (p : Ideal (𝓞 E)) [p.IsPrime] (a : 𝓞 E) : (a : E) ∈ locInt p :=
  ⟨1, one_nmem p, a, by simp⟩

theorem approx (G : 𝓞 E) (μ : E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), G ∈ P.asIdeal → (haveI := P.isPrime; μ ∈ locInt P.asIdeal)) :
    ∃ c : 𝓞 E, ∀ P : HeightOneSpectrum (𝓞 E), G ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ w : 𝓞 E, (s : E) * ((c : E) - μ) = (G : E) * w := by
  let J : Ideal (𝓞 E) :=
    { carrier := {s | ∃ a : 𝓞 E, (s : E) * μ = a}
      add_mem' := by
        rintro s t ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, by push_cast; linear_combination ha + hb⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by simp only [smul_eq_mul]; push_cast; linear_combination (c : E) * ha⟩ }
  have hJ : J ⊔ Ideal.span {G} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hne' : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
    let P : HeightOneSpectrum (𝓞 E) := ⟨M, hM.isPrime, hne'⟩
    have hG : G ∈ P.asIdeal := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self G))
    obtain ⟨s, hs, a, ha⟩ := h P hG
    have hsJ : s ∈ J := ⟨a, ha⟩
    exact hs (hle (Ideal.mem_sup_left hsJ))
  have h1 : (1 : 𝓞 E) ∈ J ⊔ Ideal.span {G} := hJ ▸ Submodule.mem_top
  obtain ⟨y, hyJ, w', hw', hyw⟩ := Submodule.mem_sup.mp h1
  obtain ⟨a, ha⟩ := hyJ
  obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
  refine ⟨a, fun P hP => ?_⟩
  obtain ⟨s, hs, b, hb⟩ := h P hP
  refine ⟨s, hs, -(w * b), ?_⟩
  have hy : (y : E) = 1 - (w : E) * G := by
    have := congrArg (fun t : 𝓞 E => (t : E)) hyw
    push_cast at this
    linear_combination this
  push_cast
  linear_combination (-(s : E)) * ha + ((s : E) * μ) * hy - (G : E) * (w : E) * hb

theorem mem_locP {p : Ideal (𝓞 E)} [p.IsPrime] {L : Submodule (𝓞 E) S.V} {v : S.V} :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • v ∈ L := by
  constructor
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h⟩
  · rintro ⟨s, hs, h⟩; exact ⟨s, hs, h⟩

theorem localization_mono {p : Ideal (𝓞 E)} [p.IsPrime] {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  obtain ⟨s, hs, hv⟩ := mem_locP.mp hv
  exact mem_locP.mpr ⟨s, hs, h hv⟩

theorem smul_mem_locP {p : Ideal (𝓞 E)} [hp : p.IsPrime] {L : Submodule (𝓞 E) S.V} {c : E} {v : S.V}
    (hc : c ∈ locInt p) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : c • v ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨s, hs, a, ha⟩ := hc
  obtain ⟨t, ht, hv⟩ := mem_locP.mp hv
  refine mem_locP.mpr ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
  have : (s * t) • (c • v) = a • (t • v) := by
    simp only [osmul, smul_smul]
    congr 1
    push_cast
    rw [← ha]; ring
  rw [this]; exact L.smul_mem a hv

theorem lin_osmul (β : S.V ≃ₗ[E] S.V) (s : 𝓞 E) (v : S.V) : β (s • v) = s • β v := by
  simp only [osmul, map_smul]

theorem localization_map₂ {p : Ideal (𝓞 E)} [p.IsPrime] {L : Submodule (𝓞 E) S.V} (β : S.V ≃ₗ[E] S.V)
    (hβ : ∀ y ∈ L, β y ∈ L) {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : β v ∈ Formalism.HermitianLatticesTheory.localization₂ p L := by
  obtain ⟨s, hs, hv⟩ := mem_locP.mp hv
  exact mem_locP.mpr ⟨s, hs, by rw [← lin_osmul]; exact hβ _ hv⟩

theorem mem_gsmul {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} {v : S.V} :
    v ∈ Ideal.span {G} • Λ ↔ ∃ w ∈ Λ, G • w = v := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]

theorem gsmul_map {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} (β : S.V ≃ₗ[E] S.V) (hβ : ∀ y ∈ Λ, β y ∈ Λ) :
    ∀ y ∈ Ideal.span {G} • Λ, β y ∈ Ideal.span {G} • Λ := by
  intro y hy
  obtain ⟨w, hw, rfl⟩ := mem_gsmul.mp hy
  exact mem_gsmul.mpr ⟨β w, hβ w hw, (lin_osmul β G w).symm⟩

theorem gsmem {p : Ideal (𝓞 E)} [hp : p.IsPrime] {G : 𝓞 E} {Λ : Submodule (𝓞 E) S.V} {d : E} {v : S.V}
    {s w : 𝓞 E} (hs : s ∉ p) (hd : (s : E) * d = (G : E) * w) (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) :
    d • v ∈ Formalism.HermitianLatticesTheory.localization₂ p (Ideal.span {G} • Λ) := by
  obtain ⟨t, ht, hv⟩ := mem_locP.mp hv
  refine mem_locP.mpr ⟨s * t, fun h => (hp.mem_or_mem h).elim hs ht, ?_⟩
  have : (s * t) • (d • v) = G • (w • (t • v)) := by
    simp only [osmul, smul_smul]
    congr 1
    push_cast
    linear_combination (t : E) * hd
  rw [this]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self G) (Λ.smul_mem w hv)

def frE {n : ℕ} (f : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) : Fin n → S.V :=
  fun b => ∑ a, A a b • f a

theorem frE_mul {n : ℕ} (f : Fin n → S.V) (A B : Matrix (Fin n) (Fin n) E) :
    frE (frE f A) B = frE f (A * B) := by
  funext b
  simp only [frE, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

theorem frE_add {n : ℕ} (f h : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) (b : Fin n) :
    frE (fun a => f a + h a) A b = frE f A b + frE h A b := by
  simp only [frE, smul_add, Finset.sum_add_distrib]

theorem frE_map {n : ℕ} (β : S.V ≃ₗ[E] S.V) (f : Fin n → S.V) (A : Matrix (Fin n) (Fin n) E) (b : Fin n) :
    β (frE f A b) = frE (fun a => β (f a)) A b := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [frE, map_sum, map_smul]

def UT {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : Prop := (∀ a b, b < a → A a b = 0) ∧ ∀ a, A a a = 1

theorem UT.mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : UT A) (hB : UT B) : UT (A * B) := by
  refine ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hA.1 a c h, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hba h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2, hB.2, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hA.1 a c h, zero_mul]
      · rw [hB.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

theorem mul_mem_locInt {p : Ideal (𝓞 E)} [p.IsPrime] {n : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ a b, A a b ∈ locInt p) (hB : ∀ a b, B a b ∈ locInt p) : ∀ a b, (A * B) a b ∈ locInt p := by
  intro a b
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hA a c) (hB c b)

theorem frame_castSucc {T : E} (F : LFlag S r T) (k : Fin r) : frame F k.castSucc = F.fl.e k := by
  simp [frame, FlagG.fvec]

theorem frame_last {T : E} (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp [frame, FlagG.fvec]

theorem frame_mem_locP {T : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hc : IsFixedConv Λ g F) (P : HeightOneSpectrum (𝓞 E)) (hP : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin (r + 1)) :
    (haveI := P.isPrime; frame F a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction a using Fin.lastCases with
  | last => rw [frame_last]; exact mem_locP.mpr ⟨1, one_nmem _, by rw [one_smul]; exact hz⟩
  | cast k =>
    rw [frame_castSucc]
    obtain ⟨c, _, hc1, heq⟩ := hc.1 P
    have hk : F.fl.e k ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
      rw [heq]
      refine mem_locP.mpr ⟨1, one_nmem _, ?_⟩
      rw [one_smul]
      refine Submodule.subset_span ⟨k, ?_⟩
      simp [hc1 hP k]
    exact localization_mono inf_le_left hk

end Gen

end PI.TCS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.AdmissibleStableUnderFrameChange
noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ y ∈ U, S.hT y v = 0 := by
  simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem z_mem_orth {T : E} (F : LFlag S r T) : F.fl.z ∈ orth S (Xsp F) := by
  rw [mem_orth]
  intro y hy
  have hy' : y ∈ Submodule.span E (Set.range F.fl.e) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; exact F.fl.z_orth a
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem coef_exists {T : E} (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V)
    (h1 : ∀ j, ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j)
    (h2 : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F) (b : Fin (r + 1)) :
    ∃ c : Fin r → E, (∀ k : Fin r, (b : ℕ) ≤ k → c k = 0) ∧
      ∑ k, c k • F.fl.e k = n (frame F b) - frame F b := by
  induction b using Fin.lastCases with
  | last =>
    have hv := h2 _ (z_mem_orth F)
    have hv' : n F.fl.z - F.fl.z ∈ Submodule.span E (Set.range F.fl.e) := hv
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hv'
    refine ⟨c, fun k hk => absurd hk (by simp), ?_⟩
    rw [frame_last, hc]
  | cast i =>
    rw [frame_castSucc]
    have hmem : F.fl.e i ∈ Xflag F ((i : ℕ) + 1) :=
      Submodule.subset_span ⟨i, (by simp : (i : ℕ) < (i : ℕ) + 1), rfl⟩
    have hv : n (F.fl.e i) - F.fl.e i ∈ Submodule.span E (F.fl.e '' {k | (k : ℕ) < i}) := h1 _ _ hmem
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hv
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact (Finsupp.mem_supported' E l).mp hl k (by simpa using hk)
    · rw [← hlc, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem coef {T : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (hz : F.fl.z ∈ Λ)
    (hc : IsFixedConv Λ g F) (n : S.V ≃ₗ[E] S.V) (hn : n ∈ NLam Λ F) :
    ∃ B : Matrix (Fin (r + 1)) (Fin (r + 1)) E, UT B ∧ (∀ b, n (frame F b) = frE (frame F) B b) ∧
      ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
        ∀ a b, (haveI := P.isPrime; B a b ∈ locInt P.asIdeal) := by
  obtain ⟨⟨_, hΛ⟩, h1, h2⟩ := hn
  have hnΛ : ∀ y ∈ Λ, n y ∈ Λ := by
    intro y hy
    rw [← hΛ]
    exact Submodule.mem_map_of_mem hy
  choose c hc0 hcs using coef_exists F n h1 h2
  let ν : Matrix (Fin (r + 1)) (Fin (r + 1)) E := fun a b => if h : (a : ℕ) < r then c b ⟨a, h⟩ else 0
  have hν0 : ∀ a b, b ≤ a → ν a b = 0 := by
    intro a b hba
    simp only [ν]
    split_ifs with h
    · exact hc0 b ⟨a, h⟩ (by simpa using hba)
    · rfl
  have hνsum : ∀ b, ∑ a, ν a b • frame F a = n (frame F b) - frame F b := by
    intro b
    rw [Fin.sum_univ_castSucc, ← hcs b]
    simp [ν, frame_castSucc]
  have hint : ∀ P : HeightOneSpectrum (𝓞 E), ((g : 𝓞 E) ∈ P.asIdeal) →
      ∀ b k, (haveI := P.isPrime; c b k ∈ locInt P.asIdeal) := by
    intro P hP b k
    haveI := P.isPrime
    have hf := frame_mem_locP Λ g F hz hc P hP b
    obtain ⟨s, hs, hsf⟩ := mem_locP.mp hf
    have hX : n (frame F b) - frame F b ∈ Xsp F := by
      rw [← hcs b]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    have hloc : n (frame F b) - frame F b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
      refine mem_locP.mpr ⟨s, hs, ?_⟩
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · rw [smul_sub, ← lin_osmul]
        exact Λ.sub_mem (hnΛ _ hsf) hsf
      · show s • (n (frame F b) - frame F b) ∈ Xsp F
        rw [osmul]
        exact Submodule.smul_mem _ _ hX
    obtain ⟨c', _, hc'1, heq⟩ := hc.1 P
    rw [heq] at hloc
    obtain ⟨t, ht, htv⟩ := mem_locP.mp hloc
    have hfun : (fun a => c' a • F.fl.e a) = F.fl.e := by
      funext a; rw [hc'1 hP a, one_smul]
    rw [hfun] at htv
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).mp htv
    have hsum : ∑ j, ((o j : E) - (t : E) * c b j) • F.fl.e j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have e1 : ∑ j, (o j : E) • F.fl.e j = ∑ j, o j • F.fl.e j := by simp only [osmul]
      rw [e1, ho, ← hcs b, osmul, Finset.smul_sum]
      simp only [smul_smul]
    have hk := Fintype.linearIndependent_iff.mp F.fl.e_indep _ hsum k
    exact ⟨t, ht, o k, by linear_combination -hk⟩
  refine ⟨1 + ν, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_, fun P hP a b => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hba).symm, hν0 a b hba.le, add_zero]
  · rw [Matrix.add_apply, Matrix.one_apply_eq, hν0 a a le_rfl, add_zero]
  · simp only [frE, Matrix.add_apply, add_smul, Finset.sum_add_distrib, hνsum b, Matrix.one_apply,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    abel
  · haveI := P.isPrime
    refine Subring.add_mem _ ?_ ?_
    · rw [Matrix.one_apply]
      split_ifs
      · exact Subring.one_mem _
      · exact Subring.zero_mem _
    · simp only [ν]
      split_ifs with h
      · exact hint P hP b ⟨a, h⟩
      · exact Subring.zero_mem _

theorem admissible_stable_under_frame_change {T T' : E} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (x F₂ : LFlag S r T')
    (hFz : F.fl.z ∈ Λ) (hFc : IsFixedConv Λ g F) (hxz : x.fl.z ∈ Λ) (hxc : IsFixedConv Λ g x)
    (hadm : IsAdmissible Λ g F x) (n : S.V ≃ₗ[E] S.V) (hn : n ∈ NLam Λ F) (m : S.V ≃ₗ[E] S.V)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame F₂ a = n (m (frame x a))) : IsAdmissible Λ g F F₂ := by
  obtain ⟨ξ, hξl, hξd, hξm⟩ := hadm
  have hnΛ : ∀ y ∈ Λ, n y ∈ Λ := by
    intro y hy
    rw [← hn.1.2]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨B, hBU, hBf, hBi⟩ := coef Λ g F hFz hFc n hn
  obtain ⟨A, hAU, hAf, hAi⟩ := coef Λ g x hxz hxc m hm
  let Ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) E := ξ.map (fun t => (t : E))
  have hΞU : UT Ξ := ⟨fun a b h => by simp [Ξ, hξl a b h], fun a => by simp [Ξ, hξd a]⟩
  let M := B * (Ξ * A)
  have hMU : UT M := hBU.mul (hΞU.mul hAU)
  have hMi : ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∀ a b, (haveI := P.isPrime; M a b ∈ locInt P.asIdeal) := by
    intro P hP
    haveI := P.isPrime
    exact mul_mem_locInt (hBi P hP) (mul_mem_locInt (fun a b => coe_mem_locInt _ (ξ a b)) (hAi P hP))
  have happ : ∀ a b, ∃ c : 𝓞 E, ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal →
      ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ w : 𝓞 E, (s : E) * ((c : E) - M a b) = ((g : 𝓞 E) : E) * w :=
    fun a b => approx _ _ (fun P hP => hMi P hP a b)
  choose c hc using happ
  let ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E) :=
    fun a b => if b < a then 0 else if a = b then 1 else c a b
  refine ⟨ξ', fun a b h => by simp [ξ', h], fun a => by simp [ξ'], fun b P hP => ?_⟩
  haveI := P.isPrime
  let ε : Fin (r + 1) → S.V := fun a => frame x a - frE (frame F) Ξ a
  have hε : ∀ a, ε a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {(g : 𝓞 E)} • Λ) := fun a => hξm a P hP
  have hxε : frame x = fun a => frE (frame F) Ξ a + ε a := by
    funext a; simp [ε]
  have e1 : n (frE (frE (frame F) Ξ) A b) = frE (frame F) M b := by
    rw [frE_mul, frE_map, show (fun a => n (frame F a)) = frE (frame F) B from funext hBf, frE_mul]
  have key : frame F₂ b = frE (frame F) M b + n (frE ε A b) := by
    rw [hfr, hAf, hxε, frE_add, map_add (f := _), e1]
  have hdiff : frame F₂ b - frameAct (frame F) ξ' b =
      n (frE ε A b) + ∑ a, (M a b - (ξ' a b : E)) • frame F a := by
    rw [key]
    simp only [frE, frameAct, sub_smul, Finset.sum_sub_distrib]
    abel
  show frame F₂ b - frameAct (frame F) ξ' b ∈ _
  rw [hdiff]
  refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun a _ => ?_)
  · refine localization_map₂ n (gsmul_map n hnΛ) ?_
    exact Submodule.sum_mem _ fun a _ => smul_mem_locP (hAi P hP a b) (hε a)
  · rcases lt_trichotomy a b with h | rfl | h
    · have hξ' : ξ' a b = c a b := by simp [ξ', not_lt.mpr h.le, h.ne]
      obtain ⟨s, hs, w, hw⟩ := hc a b P hP
      rw [hξ']
      refine gsmem (w := -w) hs ?_ (frame_mem_locP Λ g F hFz hFc P hP a)
      push_cast at hw ⊢
      linear_combination -hw
    · simp [ξ', hMU.2 a]
    · simp [ξ', h, hMU.1 a b h]

end Gen

end PI.TCS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermCarrierStability.MemSpanImageEquiv
noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

def Tr (γ : S.V ≃ₗ[E] S.V) (A₂ A : Submodule (𝓞 E) S.V) : Prop := ∀ v, v ∈ A₂ ↔ γ.symm v ∈ A

def TrE (γ : S.V ≃ₗ[E] S.V) (U₂ U : Submodule E S.V) : Prop := ∀ v, v ∈ U₂ ↔ γ.symm v ∈ U

variable {γ : S.V ≃ₗ[E] S.V}

theorem Tr.inf {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊓ B₂) (A ⊓ B) := by
  intro v
  rw [Submodule.mem_inf, Submodule.mem_inf, hA v, hB v]

theorem Tr.sup {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) :
    Tr γ (A₂ ⊔ B₂) (A ⊔ B) := by
  intro v
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨γ.symm y, (hA y).1 hy, γ.symm z, (hB z).1 hz, (map_add _ _ _).symm⟩
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨γ y, (hA _).2 (by simpa using hy), γ z, (hB _).2 (by simpa using hz), ?_⟩
    rw [← map_add (f := _), hyz, LinearEquiv.apply_symm_apply]

theorem TrE.toO {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) : Tr γ (toO S U₂) (toO S U) := by
  intro v
  exact h v

theorem Tr.localization₂ {p : Ideal (𝓞 E)} [p.IsPrime] {A₂ A : Submodule (𝓞 E) S.V} (h : Tr γ A₂ A) :
    Tr γ (Formalism.HermitianLatticesTheory.localization₂ p A₂) (Formalism.HermitianLatticesTheory.localization₂ p A) := by
  intro v
  rw [mem_locP, mem_locP]
  refine exists_congr (fun s => and_congr_right (fun _ => ?_))
  rw [h, lin_osmul]

theorem Tr.eq {A₂ A B₂ B : Submodule (𝓞 E) S.V} (hA : Tr γ A₂ A) (hB : Tr γ B₂ B) (h : A = B) :
    A₂ = B₂ := by
  ext v
  rw [hA, hB, h]

theorem mem_span_image_equiv {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] (β : M ≃ₗ[R] M)
    (s : Set M) (v : M) : v ∈ Submodule.span R (β '' s) ↔ β.symm v ∈ Submodule.span R s := by
  have hs : (β '' s) = (β : M →ₗ[R] M) '' s := rfl
  rw [hs, Submodule.span_image, Submodule.mem_map_equiv]

theorem Tr.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : Tr γ (Submodule.span (𝓞 E) s₂) (Submodule.span (𝓞 E) s) := by
  subst h
  intro v
  exact mem_span_image_equiv (γ.restrictScalars (𝓞 E)) s v

theorem TrE.span {s₂ s : Set S.V} (h : s₂ = γ '' s) : TrE γ (Submodule.span E s₂) (Submodule.span E s) := by
  subst h
  intro v
  exact mem_span_image_equiv γ s v

theorem tr_of_gmap {Λ : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap γ Λ = Λ) : Tr γ Λ Λ := by
  intro v
  constructor
  · intro hv
    rw [← h] at hv
    unfold Formalism.HermitianLatticesTheory.gmap at hv
    rw [Submodule.mem_map] at hv
    obtain ⟨y, hy, rfl⟩ := hv
    simpa using hy
  · intro hv
    rw [← h]
    unfold Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.mem_map]
    exact ⟨γ.symm v, hv, by simp⟩

theorem TrE.perp {U₂ U : Submodule E S.V} (h : TrE γ U₂ U) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) :
    TrE γ (Formalism.MainNotions.S.Lat.orth S U₂) (Formalism.MainNotions.S.Lat.orth S U) := by
  intro v
  simp only [Formalism.MainNotions.S.Lat.orth, Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro hv y hy
    have hgy : γ y ∈ U₂ := (h _).2 (by simpa using hy)
    rw [← hiso y (γ.symm v), LinearEquiv.apply_symm_apply]
    exact hv _ hgy
  · intro hv y hy
    have h1 := hv _ ((h y).1 hy)
    rw [← hiso, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1

variable {T' : E} {x F₂ : LFlag S r T'}

theorem trE_Xsp (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) : TrE γ (Xsp F₂) (Xsp x) := by
  have hs : Set.range F₂.fl.e = γ '' Set.range x.fl.e := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext he)
  exact TrE.span hs

theorem tr_XLam (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    Tr γ (XLam Λ F₂) (XLam Λ x) := by
  unfold XLam
  exact Tr.inf hΛ (TrE.toO (trE_Xsp he))

theorem tr_Lsub (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) : Tr γ (Lsub Λ F₂) (Lsub Λ x) := by
  have hX := trE_Xsp he
  have hO := TrE.toO (TrE.perp hX hiso)
  unfold Lsub Lrep
  exact Tr.inf (Tr.sup (Tr.inf hΛ hO) (TrE.toO hX)) hO

theorem isLift_tr (Λ : Submodule (𝓞 E) S.V) (hΛ : Tr γ Λ Λ) (hz : F₂.fl.z = γ x.fl.z)
    (hzt : F₂.zt = γ x.zt) (hx : IsLift Λ x) : IsLift Λ F₂ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [hz]
    exact (hΛ _).2 (by simpa using h1)
  · rw [hzt, hz, h2]

theorem fixedConv_tr (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (hΛ : Tr γ Λ Λ) (he : ∀ k, F₂.fl.e k = γ (x.fl.e k))
    (hz : F₂.fl.z = γ x.fl.z) (hiso : ∀ a b, S.hT (γ a) (γ b) = S.hT a b) (hx : IsFixedConv Λ g x) :
    IsFixedConv Λ g F₂ := by
  obtain ⟨h1, h2⟩ := hx
  refine ⟨fun P => ?_, fun c hc => ?_⟩
  · obtain ⟨c, hc0, hc1, hloc⟩ := h1 P
    refine ⟨c, hc0, hc1, ?_⟩
    haveI := P.isPrime
    have hs : Set.range (fun a => c a • F₂.fl.e a) = γ '' Set.range (fun a => c a • x.fl.e a) := by
      rw [← Set.range_comp]
      congr 1
      funext a
      simp [he a]
    exact Tr.eq (Tr.localization₂ (tr_XLam Λ hΛ he)) (Tr.localization₂ (Tr.span hs)) hloc
  · apply h2 c
    have h3 := (tr_Lsub Λ hΛ he hiso (c • F₂.fl.z)).1 hc
    rw [hz, map_smul, LinearEquiv.symm_apply_apply] at h3
    exact h3

end Gen

end PI.TCS
end
end

noncomputable section

open scoped Classical

namespace PI.TCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tr_XS (D : D7) {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (D.sp.Y 0) D.R.rS T'} (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) :
    Tr γ (XS D F₂.fl) (XS D x.fl) := by
  intro v
  have hmap : XS D F₂.fl = (XS D x.fl).map
      ((γ.restrictScalars (𝓞 D.host.E) : (VS D).V ≃ₗ[𝓞 D.host.E] (VS D).V) :
        (VS D).V →ₗ[𝓞 D.host.E] (VS D).V) := by
    unfold XS
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, c, hc, rfl⟩
      exact ⟨c • x.fl.e a, ⟨a, c, hc, rfl⟩, by simp [he]⟩
    · rintro ⟨_, ⟨a, c, hc, rfl⟩, rfl⟩
      exact ⟨a, c, hc, by simp [he]⟩
  rw [hmap, Submodule.mem_map_equiv]
  rfl

theorem frameOK_tr (D : D7) {T' : D.host.E} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {x F₂ : LFlag (D.sp.Y 0) D.R.rS T'} (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Tr γ Λ Λ)
    (he : ∀ k, F₂.fl.e k = γ (x.fl.e k)) (hz : F₂.fl.z = γ x.fl.z)
    (hiso : ∀ a b, (VS D).hT (γ a) (γ b) = (VS D).hT a b) (hx : FrameOK D Λ x) : FrameOK D Λ F₂ :=
  ⟨fixedConv_tr Λ (gS D) hΛ he hz hiso hx.1, Tr.eq (tr_XLam Λ hΛ he) (tr_XS D he) hx.2⟩

theorem termStable_holds (D : D7) (u u' : D.what₂.Word) : TermStable D u u' := by
  intro F0 Λ hΛ x F₂ hDC
  obtain ⟨hxl, hxa, hxf⟩ := x.2
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hDC
  obtain ⟨_, ⟨_, _, hFl, hFc⟩, _⟩ := hΛ
  have hΛn : Tr n Λ Λ := tr_of_gmap hn.1.2
  have hΛm : Tr m Λ Λ := tr_of_gmap hm.1.2
  have hΛγ : Tr (m.trans n) Λ Λ := by
    intro v
    rw [LinearEquiv.symm_trans_apply, ← hΛm, ← hΛn]
  have hn1 : ∀ a b, (VS D).hT (n a) (n b) = (VS D).hT a b := hn.1.1
  have hm1 : ∀ a b, (VS D).hT (m a) (m b) = (VS D).hT a b := hm.1.1
  have hiso : ∀ a b, (VS D).hT ((m.trans n) a) ((m.trans n) b) = (VS D).hT a b := by
    intro a b
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hn1, hm1]
  have he : ∀ k, F₂.fl.e k = (m.trans n) (x.1.fl.e k) := by
    intro k
    have := hfr k.castSucc
    rwa [frame_castSucc, frame_castSucc] at this
  have hz : F₂.fl.z = (m.trans n) x.1.fl.z := by
    have := hfr (Fin.last _)
    rwa [frame_last, frame_last] at this
  exact ⟨isLift_tr Λ hΛγ hz hzt hxl,
    admissible_stable_under_frame_change Λ (gS D) (lf D F0) x.1 F₂ hFl.1 hFc hxl.1 hxf.1 hxa n hn m hm hfr,
    frameOK_tr D Λ hΛγ he hz hiso hxf⟩

end D7

end PI.TCS
