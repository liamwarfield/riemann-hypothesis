module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLattices
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemFlagUnipotentIffOrderedEichlerProduct
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSymplecticBasisLocalExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagUnipotentNormalFormRescaled
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagUnipotentNormalFormRescaled
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.NormalFormRescaled

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem eich_smul_base (c : E) (hc : L.cj c = c) (x u : Fin n → E) (s : E) (v : Fin n → E) :
    eich L Hm (c • x) u s v = eich L Hm x (c • u) (c ^ 2 * s) v := by
  simp only [eich, Eichler.hf_smul_r, Eichler.hf_smul_l, hc]
  module

theorem cj_alg (a : F) : L.cj (algebraMap F E a) = algebraMap F E a := L.cj.commutes a

omit [TopologicalSpace E] in
theorem alg_inv_mul (a : Fˣ) : algebraMap F E ((a⁻¹ : Fˣ) : F) * algebraMap F E (a : F) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

omit [TopologicalSpace E] in
theorem alg_mul_inv (a : Fˣ) : algebraMap F E (a : F) * algebraMap F E ((a⁻¹ : Fˣ) : F) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

end

end GlobalTheory.HL.NormalFormRescaled

open GlobalTheory.HL.NormalFormRescaled in
theorem GlobalTheory.HL.nof_normal_form_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs hsel a X Y hX hY
  have hgg : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (g j.castSucc) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.gram]; simp [Fin.castSucc_ne_last]
    · rw [S.gram']; simp [Fin.castSucc_ne_last]
  have hgs : ∀ i j : Fin r, hf L S.Hm (g i.castSucc) (gs j) = if i = j then 1 else 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · rw [S.dual]; simp [Fin.castSucc_inj]
    · rw [S.dual']; simp [Fin.castSucc_inj]
  have hss : ∀ i j : Fin r, hf L S.Hm (gs i) (gs j) = 0 := by
    intro i j
    rcases hsel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2
    · exact S.iso i j
    · exact S.iso' i j
  have hg : ∀ i, g i.castSucc = algebraMap F E ((a i)⁻¹ : Fˣ) • X i := by
    intro i; rw [← hX i, smul_smul, alg_inv_mul, one_smul]
  have hY' : ∀ i, Y i = algebraMap F E ((a i)⁻¹ : Fˣ) • gs i := by
    intro i; rw [hY i, smul_smul, alg_inv_mul, one_smul]
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, fun n => ?_⟩
  · simp only [Frames.h]
    rw [← hX i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, hgs]
    split_ifs with h
    · subst h; rw [mul_one, alg_mul_inv]
    · simp
  · simp only [Frames.h]
    rw [← hX i, ← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, hgg]; simp
  · simp only [Frames.h]
    rw [hY' i, hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, hss]; simp
  rw [GlobalTheory.T.mem_flagUnipotent_iff_orderedEichlerProduct L r k S g gs hsel n]
  constructor
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E ((a i)⁻¹ : Fˣ) • u i,
      fun i => algebraMap F E ((a i)⁻¹ : Fˣ) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [← hX j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY' j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _)]
  · rintro ⟨u, s, e, he, hn⟩
    refine ⟨fun i => algebraMap F E (a i : F) • u i,
      fun i => algebraMap F E (a i : F) ^ 2 * s i, e, fun i => ?_, hn⟩
    obtain ⟨ho, hs, hev⟩ := he i
    refine ⟨fun j hj => ?_, ?_, fun v => ?_⟩
    · obtain ⟨h1, h2⟩ := ho j hj
      simp only [Frames.h] at h1 h2 ⊢
      constructor
      · rw [hg j, Eichler.hf_smul_l, Eichler.hf_smul_r, h1]; simp
      · rw [hY j, Eichler.hf_smul_l, Eichler.hf_smul_r, h2]; simp
    · simp only [Frames.h] at hs ⊢
      rw [map_mul, map_pow, cj_alg, Eichler.hf_smul_l, Eichler.hf_smul_r, cj_alg, ← hs]; ring
    · rw [hev v, hg i, eich_smul_base L _ _ (cj_alg L _), smul_smul, ← mul_assoc, ← mul_pow,
        alg_inv_mul, one_pow, one_mul, one_smul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagUnipotentNormalFormRescaledStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hsel : (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es')) (a : Fin r → Fˣ) (X Y : Fin r → S.V) (hX : ∀ i, algebraMap F E (a i) • g i.castSucc = X i) (hY : ∀ i, gs i = algebraMap F E (a i) • Y i), (∀ i j, S.h (X i) (Y j) = if i = j then 1 else 0) ∧ (∀ i j, S.h (X i) (X j) = 0) ∧ (∀ i j, S.h (Y i) (Y j) = 0) ∧ ∀ n : S.GLV, n ∈ S.Nof g ↔ ∃ (u : Fin r → S.V) (s : Fin r → E) (e : Fin r → S.GLV), (∀ i, (∀ j, j ≤ i → S.h (u i) (X j) = 0 ∧ S.h (u i) (Y j) = 0) ∧ s i + L.cj (s i) = S.h (u i) (u i) ∧ ∀ v, e i v = eich L S.Hm (X i) (u i) (s i) v) ∧ n = (List.ofFn e).prod := by
  first | exact @GlobalTheory.HL.nof_normal_form_rescaled | exact GlobalTheory.HL.nof_normal_form_rescaled | (intros; apply GlobalTheory.HL.nof_normal_form_rescaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLattice
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.HL.EichCont

section Abstract

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}

def IntV (v : Fin N → E) : Prop := ∀ j, v j ∈ O

def Bd (A : Module.End E (Fin N → E)) (t : F) : Prop :=
  ∀ m, IntV O m → ∃ m', IntV O m' ∧ A m = algebraMap F E t • m'

variable {O}

variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

end Abstract

section Eich

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E)

end Eich

section Lat

variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {O : Subring E} {N : ℕ}
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O)
include hden

end Lat

private lemma exists_algebraMap_mul_mem_O {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (z : E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧ algebraMap F E a * z ∈ L.O := by
  have hint : ∀ t : F, ∃ s : F, s ≠ 0 ∧ s ∈ (valuation F).integer ∧
      s * t ∈ (valuation F).integer := by
    intro t
    by_cases ht : valuation F t ≤ 1
    · exact ⟨1, one_ne_zero, (valuation F).integer.one_mem, by
        rw [one_mul, Valuation.mem_integer_iff]; exact ht⟩
    · have ht0 : t ≠ 0 := by rintro rfl; exact ht (by simp)
      refine ⟨t⁻¹, inv_ne_zero ht0, ?_, by
        rw [inv_mul_cancel₀ ht0]; exact (valuation F).integer.one_mem⟩
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 ht))
  obtain ⟨ω, hωO, e, -, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  obtain ⟨x, y, hxy⟩ := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := F) (L.cj : E →+* E)
    (fun x => L.cj_cj x) (fun r => L.cj.commutes r)
    (fun x hx => by obtain ⟨a, ha⟩ := (L.cj_fix x).1 hx; exact ⟨a, ha⟩)
    ⟨⟨_, e, hωe, by rw [mul_comm]; exact hωe⟩, rfl⟩ z
  obtain ⟨s₁, hs₁0, hs₁, hs₁x⟩ := hint x
  obtain ⟨s₂, hs₂0, hs₂, hs₂y⟩ := hint y
  have hO : ∀ t ∈ (valuation F).integer, algebraMap F E t ∈ L.O :=
    fun t ht => (_root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L t).2 ht
  refine ⟨s₁ * s₂, mul_ne_zero hs₁0 hs₂0, hO _ ((valuation F).integer.mul_mem hs₁ hs₂), ?_⟩
  rw [hxy]
  have : algebraMap F E (s₁ * s₂) * (algebraMap F E x + algebraMap F E y * ω) =
      algebraMap F E s₂ * algebraMap F E (s₁ * x) +
        algebraMap F E s₁ * algebraMap F E (s₂ * y) * ω := by
    simp only [map_mul]; ring
  rw [this]
  exact L.O.add_mem (L.O.mul_mem (hO _ hs₂) (hO _ hs₁x))
    (L.O.mul_mem (L.O.mul_mem (hO _ hs₁) (hO _ hs₂y)) hωO)

section
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] (O : Subring E) {N : ℕ}

variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mul_mem_O_forall {κ : Type} [Fintype κ] (z : κ → E) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ ∀ k, algebraMap F E a * z k ∈ O := by
  choose a ha0 haO haz using fun k => hden (z k)
  refine ⟨∏ k, a k, Finset.prod_ne_zero_iff.2 fun k _ => ha0 k, ?_, fun k => ?_⟩
  · rw [map_prod]
    exact O.prod_mem fun k _ => haO k
  · rw [map_prod, ← Finset.prod_erase_mul _ _ (Finset.mem_univ k), mul_assoc]
    exact O.mul_mem (O.prod_mem fun k' _ => haO k') (haz k)

variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_algebraMap_mem_O_Bd_inv (A : Module.End E (Fin N → E)) :
    ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ _root_.GlobalTheory.HL.EichCont.Bd O A a⁻¹ := by
  obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : Fin N × Fin N => A (fun k => if p.1 = k then 1 else 0) p.2)
  refine ⟨a, ha0, haO, fun m hm => ⟨algebraMap F E a • A m, fun i => ?_, ?_⟩⟩
  · rw [LinearMap.pi_apply_eq_sum_univ A m]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, Finset.mul_sum]
    exact O.sum_mem fun j _ => by
      rw [mul_left_comm]
      exact O.mul_mem (hm j) (haz (j, i))
  · rw [smul_smul, ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]

variable {O} in
private lemma Bd_zero' (t : F) : _root_.GlobalTheory.HL.EichCont.Bd O (0 : Module.End E (Fin N → E)) t :=
  fun _ _ => ⟨0, fun _ => O.zero_mem, by simp⟩

variable {O} in
private lemma IntV_smul_of_mem {o : E} (ho : o ∈ O) {m : Fin N → E}
    (hm : _root_.GlobalTheory.HL.EichCont.IntV O m) : _root_.GlobalTheory.HL.EichCont.IntV O (o • m) :=
  fun j => by simpa using O.mul_mem ho (hm j)

variable {O} in
private lemma Bd_of_Bd_mul_of_mem_O {A : Module.End E (Fin N → E)} {s o : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A (s * o)) (ho : algebraMap F E o ∈ O) :
    _root_.GlobalTheory.HL.EichCont.Bd O A s := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  exact ⟨algebraMap F E o • m₁, IntV_smul_of_mem ho hm₁, by rw [e₁, map_mul, mul_smul]⟩

variable {O} in
private lemma Bd_of_eq {A : Module.End E (Fin N → E)} {s t : F} (h : s = t)
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) : _root_.GlobalTheory.HL.EichCont.Bd O A t := h ▸ hA

variable {O} in
private lemma IntV_add' {m m' : Fin N → E} (hm : _root_.GlobalTheory.HL.EichCont.IntV O m)
    (hm' : _root_.GlobalTheory.HL.EichCont.IntV O m') : _root_.GlobalTheory.HL.EichCont.IntV O (m + m') :=
  fun j => O.add_mem (hm j) (hm' j)

variable {O} in
private lemma Bd_add' {A B : Module.End E (Fin N → E)} {t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A t) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A + B) t := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hA m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hB m hm
  exact ⟨m₁ + m₂, IntV_add' hm₁ hm₂, by rw [LinearMap.add_apply, e₁, e₂, smul_add]⟩

variable {O} in
private lemma Bd_mul' {A B : Module.End E (Fin N → E)} {s t : F}
    (hA : _root_.GlobalTheory.HL.EichCont.Bd O A s) (hB : _root_.GlobalTheory.HL.EichCont.Bd O B t) :
    _root_.GlobalTheory.HL.EichCont.Bd O (A * B) (s * t) := by
  intro m hm
  obtain ⟨m₁, hm₁, e₁⟩ := hB m hm
  obtain ⟨m₂, hm₂, e₂⟩ := hA m₁ hm₁
  refine ⟨m₂, hm₂, ?_⟩
  rw [Module.End.mul_apply, e₁, map_smul, e₂, smul_smul, ← map_mul, mul_comm t s]

variable {O} in
variable (hden : ∀ z : E, ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ O ∧ algebraMap F E a * z ∈ O) in
include hden in
private lemma exists_Bd_prod_sub_of_Bd_sub : ∀ (r : ℕ) (A : Fin r → Module.End E (Fin N → E)) (c : F),
    c ≠ 0 → ∃ d : F, d ≠ 0 ∧ ∀ G : Fin r → Module.End E (Fin N → E),
      (∀ i, _root_.GlobalTheory.HL.EichCont.Bd O (G i - A i) d) →
        _root_.GlobalTheory.HL.EichCont.Bd O ((List.ofFn G).prod - (List.ofFn A).prod) c := by
  intro r
  induction r with
  | zero =>
    intro A c _
    exact ⟨1, one_ne_zero, fun G _ => by
      simp only [List.ofFn_zero, List.prod_nil, sub_self]
      exact Bd_zero' c⟩
  | succ r ih =>
    intro A c hc
    obtain ⟨a, ha0, haO, hA0⟩ := exists_algebraMap_mem_O_Bd_inv hden (A 0)
    obtain ⟨b, hb0, hbO, hAs⟩ := exists_algebraMap_mem_O_Bd_inv hden (List.ofFn fun i => A i.succ).prod
    obtain ⟨w, hw0, hwO, hwc⟩ := hden (algebraMap F E c)
    obtain ⟨d₁, hd₁0, hd₁⟩ := ih (fun i => A i.succ) (c * a * b * w) (by simp [hc, ha0, hb0, hw0])
    obtain ⟨z, hz0, hzO, hz⟩ := exists_algebraMap_mul_mem_O_forall hden
      ![algebraMap F E (c * b), algebraMap F E d₁]
    have hz1 : algebraMap F E z * algebraMap F E (c * b) ∈ O := hz 0
    have hz2 : algebraMap F E z * algebraMap F E d₁ ∈ O := hz 1
    refine ⟨c * b * d₁ * z, by simp [hc, hb0, hd₁0, hz0], fun G hG => ?_⟩
    have hG0 : _root_.GlobalTheory.HL.EichCont.Bd O (G 0 - A 0) (c * b) :=
      Bd_of_Bd_mul_of_mem_O (o := d₁ * z) (Bd_of_eq (by ring) (hG 0))
        (by rw [map_mul, mul_comm]; exact hz2)
    have hGs : ∀ i : Fin r, _root_.GlobalTheory.HL.EichCont.Bd O (G i.succ - A i.succ) d₁ := fun i =>
      Bd_of_Bd_mul_of_mem_O (o := c * b * z) (Bd_of_eq (by ring) (hG i.succ))
        (by rw [map_mul, mul_comm]; exact hz1)
    have hrest := hd₁ (fun i => G i.succ) hGs
    have hGsb : _root_.GlobalTheory.HL.EichCont.Bd O (List.ofFn fun i => G i.succ).prod b⁻¹ := by
      have h1 : _root_.GlobalTheory.HL.EichCont.Bd O
          ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) b⁻¹ :=
        Bd_of_Bd_mul_of_mem_O (o := c * a * b * w * b) (Bd_of_eq (by field_simp) hrest) (by
          have := O.mul_mem (O.mul_mem (O.mul_mem hwc haO) hbO) hbO
          simp only [map_mul]
          convert this using 1
          ring)
      have := Bd_add' hAs h1
      rwa [add_sub_cancel] at this
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons]
    have key : G 0 * (List.ofFn fun i => G i.succ).prod - A 0 * (List.ofFn fun i => A i.succ).prod =
        (G 0 - A 0) * (List.ofFn fun i => G i.succ).prod +
          A 0 * ((List.ofFn fun i => G i.succ).prod - (List.ofFn fun i => A i.succ).prod) := by
      rw [sub_mul, mul_sub]
      abel
    rw [key]
    refine Bd_add' ?_ ?_
    · exact Bd_of_eq (by field_simp) (Bd_mul' hG0 hGsb)
    · exact Bd_of_Bd_mul_of_mem_O (o := b * w) (Bd_of_eq (by field_simp) (Bd_mul' hA0 hrest))
        (by rw [map_mul]; exact O.mul_mem hbO hwO)
end

theorem _root_.GlobalTheory.HL.EichCont.prod_eich_cont : ∀ {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E)
    (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E))
    (he : ∀ i v, e i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v)
    (Λ : Submodule L.O (Fin N → E)) (hΛ : _root_.GlobalTheory.HL.IsLat L Λ) (c : Fˣ),
    ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E)
      (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)),
      (∀ i v, e' i v = _root_.GlobalTheory.HL.eich L Hm (X i) (u' i) (s' i) v) →
      (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) →
      (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) →
      ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x =
        algebraMap F E c • y := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm X u s e he Λ hΛ c
  have hden := exists_algebraMap_mul_mem_O L
  obtain ⟨β, hβ0, hβO, hβ⟩ := exists_algebraMap_mul_mem_O_forall hden
    (fun p : (Fin N × Fin N) ⊕ (Fin r × Fin N) =>
      Sum.elim (fun q => Hm q.1 q.2) (fun q => X q.1 q.2) p)
  have hH : ∀ i j, algebraMap F E β * Hm i j ∈ L.O := fun i j => hβ (Sum.inl (i, j))
  have hX : ∀ i k, algebraMap F E β * X i k ∈ L.O := fun i k => hβ (Sum.inr (i, k))
  have hXc : ∀ i k, algebraMap F E β * L.cj (X i k) ∈ L.O := fun i k => by
    have := _root_.GlobalTheory.UnramOrder.cj_mem L (hX i k)
    rwa [map_mul, L.cj.commutes] at this

  have hform1 : ∀ v o : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → _root_.GlobalTheory.HL.EichCont.IntV L.O o →
      algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v o ∈ L.O := by
    intro v o hv ho
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (_root_.GlobalTheory.UnramOrder.cj_mem L (ho b))
    convert this using 1
    ring
  have hform2 : ∀ v : Fin N → E, _root_.GlobalTheory.HL.EichCont.IntV L.O v → ∀ i,
      algebraMap F E β * algebraMap F E β * _root_.GlobalTheory.HL.hf L Hm v (X i) ∈ L.O := by
    intro v hv i
    unfold _root_.GlobalTheory.HL.hf
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun a _ => ?_
    rw [Finset.mul_sum]
    refine L.O.sum_mem fun b _ => ?_
    have := L.O.mul_mem (L.O.mul_mem (hv a) (hH a b)) (hXc i b)
    convert this using 1
    ring
  have hsub : ∀ v w w' : Fin N → E, _root_.GlobalTheory.HL.hf L Hm v w -
      _root_.GlobalTheory.HL.hf L Hm v w' = _root_.GlobalTheory.HL.hf L Hm v (w - w') := by
    intro v w w'
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]
  have hsmul : ∀ (v o : Fin N → E) (t : F), _root_.GlobalTheory.HL.hf L Hm v
      (algebraMap F E t • o) = algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
    intro v o t
    unfold _root_.GlobalTheory.HL.hf
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hdiff : ∀ i (u₁ : Fin N → E) (s₁ : E) (t : F) (o : Fin N → E) (o' : E) (v : Fin N → E),
      u₁ - u i = algebraMap F E t • o → s₁ - s i = algebraMap F E t * o' →
      _root_.GlobalTheory.HL.eich L Hm (X i) u₁ s₁ v - _root_.GlobalTheory.HL.eich L Hm (X i) (u i) (s i) v =
        algebraMap F E t • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
          _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i)) := by
    intro i u₁ s₁ t o o' v hu hs
    have hu' : u₁ = u i + algebraMap F E t • o := by rw [← hu]; abel
    have hs' : s₁ = s i + algebraMap F E t * o' := by rw [← hs]; ring
    have h1 : _root_.GlobalTheory.HL.hf L Hm v u₁ = _root_.GlobalTheory.HL.hf L Hm v (u i) +
        algebraMap F E t * _root_.GlobalTheory.HL.hf L Hm v o := by
      rw [← hsmul, ← hu, ← hsub]; ring
    unfold _root_.GlobalTheory.HL.eich
    rw [h1, hu', hs']
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hbr : ∀ i (o : Fin N → E) (o' : E) (v : Fin N → E), _root_.GlobalTheory.HL.EichCont.IntV L.O v →
      _root_.GlobalTheory.HL.EichCont.IntV L.O o → o' ∈ L.O →
      _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E (β ^ 3) • (_root_.GlobalTheory.HL.hf L Hm v o • X i -
        _root_.GlobalTheory.HL.hf L Hm v (X i) • (o + o' • X i))) := by
    intro i o o' v hv ho ho' k
    have t1 := L.O.mul_mem (L.O.mul_mem (hform1 v o hv ho) (hX i k)) hβO
    have t2 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) hβO) (ho k)
    have t3 := L.O.mul_mem (L.O.mul_mem (hform2 v hv i) ho') (hX i k)
    have := L.O.sub_mem t1 (L.O.add_mem t2 t3)
    convert this using 1
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul, map_pow]
    ring
  let φ : ((Fin N → E) ≃ₗ[E] (Fin N → E)) →* Module.End E (Fin N → E) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hP : ∀ (f : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (y : Fin N → E),
      (List.ofFn f).prod y = (List.ofFn fun i => φ (f i)).prod y := by
    intro f y
    have : φ (List.ofFn f).prod = (List.ofFn fun i => φ (f i)).prod := by
      rw [map_list_prod, List.map_ofFn]; rfl
    rw [← this]; rfl
  obtain ⟨a, ha0, haO, ha⟩ : ∃ a : F, a ≠ 0 ∧ algebraMap F E a ∈ L.O ∧
      ∀ x ∈ Λ, _root_.GlobalTheory.HL.EichCont.IntV L.O (algebraMap F E a • x) := by
    obtain ⟨S, hS⟩ := hΛ.1
    obtain ⟨a, ha0, haO, haz⟩ := exists_algebraMap_mul_mem_O_forall hden
      (fun p : S × Fin N => (p.1 : Fin N → E) p.2)
    refine ⟨a, ha0, haO, fun x hx => ?_⟩
    rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact fun j => haz (⟨y, hy⟩, j)
    | zero => exact fun j => by simp
    | add y z _ _ hy hz => exact fun j => by simpa [mul_add] using L.O.add_mem (hy j) (hz j)
    | smul o y _ hy =>
      exact fun j => by simpa [Subring.smul_def, mul_left_comm] using L.O.mul_mem o.2 (hy j)
  obtain ⟨b, hb0, hbO, hb⟩ : ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧
      ∀ m, _root_.GlobalTheory.HL.EichCont.IntV L.O m → algebraMap F E b • m ∈ Λ := by
    have hstep : ∀ w ∈ Submodule.span E (Λ : Set (Fin N → E)),
        ∃ b : F, b ≠ 0 ∧ algebraMap F E b ∈ L.O ∧ algebraMap F E b • w ∈ Λ := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem y hy => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simpa using hy⟩
      | zero => exact ⟨1, one_ne_zero, by simp [L.O.one_mem], by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨b₂, h₂0, h₂O, h₂⟩ := hz
        refine ⟨b₁ * b₂, mul_ne_zero h₁0 h₂0, by rw [map_mul]; exact L.O.mul_mem h₁O h₂O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E b₂, h₂O⟩ : L.O) h₁
        have e2 := Λ.smul_mem (⟨algebraMap F E b₁, h₁O⟩ : L.O) h₂
        have := Λ.add_mem e1 e2
        convert this using 1
        simp only [Subring.smul_def, smul_smul, map_mul, smul_add, mul_comm]
      | smul t y _ hy =>
        obtain ⟨b₁, h₁0, h₁O, h₁⟩ := hy
        obtain ⟨w₁, hw0, hwO, hwt⟩ := hden t
        refine ⟨w₁ * b₁, mul_ne_zero hw0 h₁0, by rw [map_mul]; exact L.O.mul_mem hwO h₁O, ?_⟩
        have e1 := Λ.smul_mem (⟨algebraMap F E w₁ * t, hwt⟩ : L.O) h₁
        convert e1 using 1
        rw [Subring.smul_def, smul_smul, smul_smul, map_mul]
        congr 1
        show _ = algebraMap F E w₁ * t * algebraMap F E b₁
        ring
    choose bj hbj0 hbjO hbj using fun j : Fin N =>
      hstep (fun k => if j = k then (1 : E) else 0) (by rw [hΛ.2]; exact Submodule.mem_top)
    refine ⟨∏ j, bj j, Finset.prod_ne_zero_iff.2 fun j _ => hbj0 j,
      by rw [map_prod]; exact L.O.prod_mem fun j _ => hbjO j, fun m hm => ?_⟩
    have hej : ∀ j, algebraMap F E (∏ k, bj k) • (fun k => if j = k then (1 : E) else 0) ∈ Λ := by
      intro j
      have hO' : algebraMap F E (∏ k ∈ Finset.univ.erase j, bj k) ∈ L.O := by
        rw [map_prod]; exact L.O.prod_mem fun k _ => hbjO k
      have := Λ.smul_mem (⟨_, hO'⟩ : L.O) (hbj j)
      rwa [Subring.smul_def, smul_smul, ← map_mul,
        Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at this
    rw [pi_eq_sum_univ m, Finset.smul_sum]
    refine Λ.sum_mem fun j _ => ?_
    rw [smul_comm]
    exact Λ.smul_mem (⟨m j, hm j⟩ : L.O) (hej j)
  obtain ⟨γ, hγ0, -, hγ⟩ := exists_algebraMap_mem_O_Bd_inv hden
    ((List.ofFn e).prod.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)).toLinearMap
  obtain ⟨d₀, hd₀0, hd₀⟩ := exists_Bd_prod_sub_of_Bd_sub hden r (fun i => φ (e i))
    ((c : F) * b * a * γ) (by simp [hb0, ha0, hγ0])
  refine ⟨Units.mk0 (d₀ * β ^ 3) (by simp [hd₀0, hβ0]), fun u' s' e' he' hu' hs' x hx => ?_⟩
  choose ou hou hueq using hu'
  choose os hos hseq using hs'
  have hfac : ∀ i, _root_.GlobalTheory.HL.EichCont.Bd L.O (φ (e' i) - φ (e i)) d₀ := by
    intro i m hm
    refine ⟨_, hbr i (ou i) (os i) m hm (fun j => hou i j) (hos i), ?_⟩
    have := hdiff i (u' i) (s' i) (d₀ * β ^ 3) (ou i) (os i) m
      (funext fun j => by rw [Pi.sub_apply, hueq i j, Units.val_mk0]; rfl)
      (by rw [hseq i, Units.val_mk0])
    show e' i m - e i m = _
    rw [he', he, this, smul_smul, ← map_mul]
  obtain ⟨m₁, hm₁, e₁⟩ := hd₀ (fun i => φ (e' i)) hfac _ (ha x hx)
  obtain ⟨m₂, hm₂, e₂⟩ := hγ m₁ hm₁
  have e₂' : ((List.ofFn e).prod).symm m₁ = algebraMap F E γ⁻¹ • m₂ := e₂
  refine ⟨algebraMap F E b • m₂, hb m₂ hm₂, ?_⟩
  have hx' : (List.ofFn e').prod x - (List.ofFn e).prod x = algebraMap F E a⁻¹ •
      (algebraMap F E ((c : F) * b * a * γ) • m₁) := by
    rw [← e₁, LinearMap.sub_apply, ← hP e', ← hP e, map_smul, map_smul, ← smul_sub, smul_smul,
      ← map_mul, inv_mul_cancel₀ ha0, map_one, one_smul]
  calc ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x
      = ((List.ofFn e).prod).symm ((List.ofFn e').prod x - (List.ofFn e).prod x) := by
        rw [map_sub, LinearEquiv.symm_apply_apply]
    _ = algebraMap F E (c : F) • algebraMap F E b • m₂ := by
        rw [hx', smul_smul, ← map_mul, map_smul, e₂', smul_smul, ← map_mul, smul_smul, ← map_mul]
        congr 2
        field_simp

end GlobalTheory.HL.EichCont
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductContinuousOnLatticeStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (X u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (Λ : Submodule L.O (Fin N → E)) (hΛ : IsLat L Λ) (c : Fˣ), ∃ d : Fˣ, ∀ (u' : Fin r → Fin N → E) (s' : Fin r → E) (e' : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i v, e' i v = eich L Hm (X i) (u' i) (s' i) v) → (∀ i j, ∃ o ∈ L.O, u' i j - u i j = algebraMap F E d * o) → (∀ i, ∃ o ∈ L.O, s' i - s i = algebraMap F E d * o) → ∀ x ∈ Λ, ∃ y ∈ Λ, ((List.ofFn e).prod).symm ((List.ofFn e').prod x) - x = algebraMap F E c • y := by
  first | exact @GlobalTheory.HL.EichCont.prod_eich_cont | exact GlobalTheory.HL.EichCont.prod_eich_cont | (intros; apply GlobalTheory.HL.EichCont.prod_eich_cont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotent
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN

private theorem hf_add_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (a b y : Fin N → E) : hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp only [hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem hf_smul_left_flag_measures' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) {N : ℕ} (Hm : Matrix (Fin N) (Fin N) E)
    (c : E) (a y : Fin N → E) : hf L Hm (c • a) y = c * hf L Hm a y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem hq_sub_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a b y : Fin N → E) :
    hq sig Hm (a - b) y = hq sig Hm a y - hq sig Hm b y := by
  simp only [hq, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem hq_neg_left {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {N : ℕ}
    (Hm : Matrix (Fin N) (Fin N) E) (a y : Fin N → E) :
    hq sig Hm (-a) y = -hq sig Hm a y := by
  simp only [hq, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

private theorem algebraMap_integer_mem_O {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : LocE F E) (a : 𝒪[F]) : algebraMap F E (a : F) ∈ L.O := by
  rw [L.O_def]
  exact (isIntegral_algebraMap (x := a)).algebraMap

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k) (Λ : G.Lt) (hΛ : Submodule.IsFullLattice E Λ)
  (c : ∀ p, ((A.loc p).Fp)ˣ) (hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite)
  (n : ∀ p, (G.S p).GLV) (hn : {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite)
  (gF : ∀ p, Fin (r+1) → (G.S p).V) (gsF : ∀ p, Fin r → (G.S p).V) (X Y : Fin r → G.V)
  (hsel : ∀ p, (gF p = (G.S p).f ∧ gsF p = (G.S p).es) ∨ (gF p = (G.S p).f' ∧ gsF p = (G.S p).es'))
  (hX : ∀ p (a : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • gF p a.castSucc = A.bc p (X a))
  (hY : ∀ p (a : Fin r), gsF p a = algebraMap (A.loc p).Fp (A.loc p).Ep ((G.c p : (A.loc p).Fp) ^ (r - (a : ℕ))) • A.bc p (Y a))
  (hnN : ∀ p, n p ∈ (G.S p).Nof (gF p)) :
  ∃ g : G.GLV, (∀ p, ∃ g' ∈ (G.S p).Nof (gF p), A.Ext p g g') ∧ ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  classical
  have hinj : ∀ p, Function.Injective (A.loc p).ιE := fun p => by
    have := PlacesInt.nontrivial_Ep (A.loc p)
    exact (A.loc p).ιE.injective
  have hform : ∀ p (x y : Fin (k + 2 * r + 1) → E),
      (G.S p).h (A.bc p x) (A.bc p y) = (A.loc p).ιE (hq sig G.Hm x y) := by
    intro p x y
    have h := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm x y
    show hf (A.L p) (G.S p).Hm _ _ = _
    rw [G.Hm_eq p]
    exact h
  have hconj : ∀ p z, (A.L p).cj ((A.loc p).ιE z) = (A.loc p).ιE (sig z) := fun p z => by
    rw [A.L_cj p]
    exact (A.loc p).cj_ιE z
  obtain ⟨p0⟩ := exists_place F
  have hsig : ∀ z, sig (sig z) = z := fun z => by
    apply hinj p0
    rw [← hconj, ← hconj]
    exact (A.L p0).cj_cj _
  have hH : ∀ i j, sig (G.Hm j i) = G.Hm i j := fun i j => by
    have h2 := congrFun (congrFun (G.S p0).herm.1 i) j
    rw [G.Hm_eq p0] at h2
    simp only [cT, Matrix.map_apply] at h2
    apply hinj p0
    rw [← hconj]
    exact h2
  have hqsym : ∀ x y, hq sig G.Hm x y = sig (hq sig G.Hm y x) := by
    intro x y
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hq, map_sum, map_mul, hsig]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← hH j i]
    ring
  have hXa : ∀ p (i : Fin r), algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • gF p i.castSucc = A.bc p (X i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hX p i
  have hYa : ∀ p (i : Fin r), gsF p i = algebraMap (A.loc p).Fp (A.loc p).Ep
      (((G.c p ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) • A.bc p (Y i) :=
    fun p i => by
      rw [Units.val_pow_eq_pow_val]
      exact hY p i
  have hR : ∀ p, (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (Y j)) = if i = j then 1 else 0) ∧
      (∀ i j, (G.S p).h (A.bc p (X i)) (A.bc p (X j)) = 0) ∧
      (∀ i j, (G.S p).h (A.bc p (Y i)) (A.bc p (Y j)) = 0) ∧
      ∀ m : (G.S p).GLV, m ∈ (G.S p).Nof (gF p) ↔ ∃ (u : Fin r → (G.S p).V) (s : Fin r → (A.loc p).Ep)
        (e : Fin r → (G.S p).GLV), (∀ i, (∀ j, j ≤ i → (G.S p).h (u i) (A.bc p (X j)) = 0 ∧
          (G.S p).h (u i) (A.bc p (Y j)) = 0) ∧ s i + (A.L p).cj (s i) = (G.S p).h (u i) (u i) ∧
          ∀ v, e i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u i) (s i) v) ∧ m = (List.ofFn e).prod := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianFlagUnipotent_normalForm_rescaled (A.L p) r k (G.S p) (gF p) (gsF p) (hsel p) (fun i => G.c p ^ (r - (i : ℕ)))
      (fun i => A.bc p (X i)) (fun i => A.bc p (Y i)) (hXa p) (hYa p)
  choose up sp ep hup hn_eq using fun p => ((hR p).2.2.2 (n p)).1 (hnN p)
  have hXY : ∀ a b, hq sig G.Hm (X a) (Y b) = if a = b then 1 else 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).1 a b]
    split_ifs <;> simp
  have hXX : ∀ a b, hq sig G.Hm (X a) (X b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.1 a b, map_zero]
  have hYY : ∀ a b, hq sig G.Hm (Y a) (Y b) = 0 := fun a b => by
    apply hinj p0
    rw [← hform, (hR p0).2.2.1 a b, map_zero]
  set Bad : Set (HeightOneSpectrum (𝓞 F)) :=
    {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p} ∪
    {p | A.lat p Λ ≠ Submodule.span (A.L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep))} ∪
    {p | n p • A.lat p Λ ≠ A.lat p Λ} ∪
    (⋃ i, ⋃ j, {p | (A.loc p).ιE (G.Hm i j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (X a j) ∉ (A.L p).O}) ∪
    (⋃ a, ⋃ j, {p | (A.loc p).ιE (Y a j) ∉ (A.L p).O}) with hBad
  have hlatP := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  have hBadF : Bad.Finite := by
    have hi := (PlacesInt.integers_local A).2.1
    refine ((((hc.union hlatP.2.2).union hn).union ?_).union ?_).union ?_ <;>
      exact Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => hi _
  have hgood : ∀ p, p ∉ Bad →
      (∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p) ∧
      A.lat p Λ = Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin (k + 2 * r + 1) → (A.loc p).Ep)) ∧
      n p • A.lat p Λ = A.lat p Λ ∧ (∀ i j, (A.loc p).ιE (G.Hm i j) ∈ (A.L p).O) ∧
      (∀ a j, (A.loc p).ιE (X a j) ∈ (A.L p).O) ∧ (∀ a j, (A.loc p).ιE (Y a j) ∈ (A.L p).O) := by
    intro p hp
    refine ⟨Classical.byContradiction fun h => hp ?_, Classical.byContradiction fun h => hp ?_,
      Classical.byContradiction fun h => hp ?_, fun i j => Classical.byContradiction fun h => hp ?_,
      fun a j => Classical.byContradiction fun h => hp ?_, fun a j => Classical.byContradiction fun h => hp ?_⟩
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, h⟩⟩)))
    · exact Or.inl (Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩))
    · exact Or.inr (Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨j, h⟩⟩)
  have hstd : ∀ p, p ∉ Bad → ∀ x : Fin (k + 2 * r + 1) → (A.loc p).Ep,
      ((∀ j, (List.ofFn (ep p)).prod x j ∈ (A.L p).O) ↔ ∀ j, x j ∈ (A.L p).O) := by
    intro p hp x
    obtain ⟨-, hl, hnl, -⟩ := hgood p hp
    rw [← mem_coord (A.L p) ((List.ofFn (ep p)).prod x), ← mem_coord (A.L p) x, ← hl, ← hn_eq p]
    constructor
    · intro h
      rw [← hnl] at h
      obtain ⟨y, hy, hyx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
      rw [LinearEquiv.smul_def] at hyx
      rwa [← (n p).injective hyx]
    · intro h
      rw [← hnl]
      exact Submodule.smul_mem_pointwise_smul _ _ _ h
  have hint : ∀ p, p ∉ Bad → (∀ i j, up p i j ∈ (A.L p).O) ∧ ∀ i, sp p i ∈ (A.L p).O := by
    intro p hp
    obtain ⟨-, -, -, hHm, hXi, hYi⟩ := hgood p hp
    have := (A.loc p).lf
    have := (A.loc p).char0
    exact GlobalTheory.T.hermitianEichlerProduct_params_integral (A.L p) _ r (G.S p).Hm (G.S p).herm.1
      (fun i j => by rw [G.Hm_eq p]; exact hHm i j) (fun i => A.bc p (X i)) (fun i => A.bc p (Y i))
      (up p) (sp p) (ep p) (fun i j => hXi i j) (fun i j => hYi i j) (hR p).1 (hR p).2.1
      (fun i j hj => (hup p i).1 j hj) (fun i => (hup p i).2.1) (fun i v => (hup p i).2.2 v) (hstd p hp)
  have hdex : ∀ p, ∃ d : ((A.loc p).Fp)ˣ, (p ∉ Bad → d = 1) ∧
      ∀ (u' : Fin r → Fin (k + 2 * r + 1) → (A.loc p).Ep) (s' : Fin r → (A.loc p).Ep)
        (e' : Fin r → (G.S p).GLV),
        (∀ i v, e' i v = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (u' i) (s' i) v) →
        (∀ i j, ∃ o ∈ (A.L p).O, u' i j - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        (∀ i, ∃ o ∈ (A.L p).O, s' i - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d : (A.loc p).Fp) * o) →
        ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, ((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x =
          algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
    intro p
    have := (A.loc p).lf
    have := (A.loc p).char0
    by_cases hp : p ∈ Bad
    · obtain ⟨d, hd⟩ := GlobalTheory.T.hermitianEichlerProduct_continuous_on_lattice (A.L p) (k + 2 * r + 1) r (G.S p).Hm (fun i => A.bc p (X i))
        (up p) (sp p) (ep p) (fun i v => (hup p i).2.2 v) (A.lat p Λ) (hlatP.2.1 p) (c p)
      exact ⟨d, fun h => absurd hp h, hd⟩
    · refine ⟨1, fun _ => rfl, ?_⟩
      intro u' s' e' he' hu' hs' x hx
      obtain ⟨⟨cu, hcu⟩, hl, -, hHm, hXi, -⟩ := hgood p hp
      obtain ⟨hui, hsi⟩ := hint p hp
      have hu'i : ∀ i j, u' i j ∈ (A.L p).O := fun i j => by
        obtain ⟨o, ho, h⟩ := hu' i j
        have h' : u' i j - up p i j = o := by simpa using h
        rw [show u' i j = up p i j + o by rw [← h']; ring]
        exact add_mem (hui i j) ho
      have hs'i : ∀ i, s' i ∈ (A.L p).O := fun i => by
        obtain ⟨o, ho, h⟩ := hs' i
        have h' : s' i - sp p i = o := by simpa using h
        rw [show s' i = sp p i + o by rw [← h']; ring]
        exact add_mem (hsi i) ho
      have hHm' : ∀ i j, (G.S p).Hm i j ∈ (A.L p).O := fun i j => by rw [G.Hm_eq p]; exact hHm i j
      have hx' : ∀ j, x j ∈ (A.L p).O := (mem_coord (A.L p) x).1 (hl ▸ hx)
      have hz := int_prod (A.L p) hHm' r (fun i => A.bc p (X i)) u' s' e' (fun i j => hXi i j) hu'i hs'i
        he' x hx'
      have hw := (hstd p hp (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x))).1
        (by rw [LinearEquiv.apply_symm_apply]; exact hz)
      have hci : algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) ∈ (A.L p).O := by
        have : (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = ((cu⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) := by
          rw [Units.val_inv_eq_inv_val, ← hcu, eq_comm]
          apply eq_inv_of_mul_eq_one_left
          exact_mod_cast Units.inv_mul cu
        rw [this]
        exact algebraMap_integer_mem_O (A.L p) _
      refine ⟨algebraMap (A.loc p).Fp (A.loc p).Ep (((c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) •
        (((List.ofFn (ep p)).prod).symm ((List.ofFn e').prod x) - x), ?_, ?_⟩
      · rw [hl]
        refine (mem_coord (A.L p) _).2 fun j => ?_
        simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        exact mul_mem hci (sub_mem (hw j) (hx' j))
      · rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]
  choose d hd1 hd2 using hdex
  have hQex : ∀ i : Fin r, ∃ (u : Fin (k + 2 * r + 1) → E) (s : E),
      (∀ a ∈ (Finset.univ.filter fun j : Fin r => j ≤ i),
        hq sig G.Hm u (X a) = 0 ∧ hq sig G.Hm u (Y a) = 0) ∧ s + sig s = hq sig G.Hm u u ∧
      ∀ p, (∀ j, ∃ o ∈ (A.L p).O, (A.loc p).ιE (u j) - up p i j =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o) ∧
        ∃ o ∈ (A.L p).O, (A.loc p).ιE s - sp p i =
          algebraMap (A.loc p).Fp (A.loc p).Ep (d p : (A.loc p).Fp) * o := by
    intro i
    refine GlobalTheory.T.hermitian_symplectic_basis_local_extension A (k + 2 * r + 1) r G.Hm hH X Y (Finset.univ.filter fun j : Fin r => j ≤ i)
      hXY hXX hYY (fun p => up p i) (fun p => sp p i) (fun p a ha => ?_) (fun p => ?_) ?_ d ?_
    · have h := (hup p i).1 a (Finset.mem_filter.1 ha).2
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · have h := (hup p i).2.1
      simp only [Frames.h, G.Hm_eq p] at h
      exact h
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨fun j => (hint p hpb).1 i j, (hint p hpb).2 i⟩
    · exact hBadF.subset fun p hp => Classical.byContradiction fun hpb =>
        hp ⟨1, by rw [hd1 p hpb]; simp⟩
  choose uQ sQ hQ using hQex
  have hinjQ : ∀ i, Function.Injective (eQ sig G.Hm (X i) (uQ i) (sQ i)) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hv' : v + hq sig G.Hm v (uQ i) • X i - hq sig G.Hm v (X i) • (uQ i + sQ i • X i) = 0 := hv
    have hii : i ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp
    have hux : hq sig G.Hm (uQ i) (X i) = 0 := ((hQ i).1 i hii).1
    have hxu : hq sig G.Hm (X i) (uQ i) = 0 := by rw [hqsym, hux, map_zero]
    have hb : hq sig G.Hm v (X i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (X i)) hv'
      have hz0 : hq sig G.Hm 0 (X i) = 0 := by simp [hq]
      simp only [hq_sub_left, hq_add_l, hq_smul_l, hux, hXX i i, hz0] at h
      simpa using h
    rw [hb, zero_smul, sub_zero] at hv'
    have hv2 : v = -(hq sig G.Hm v (uQ i) • X i) := eq_neg_of_add_eq_zero_left hv'
    have ha : hq sig G.Hm v (uQ i) = 0 := by
      have h := congrArg (fun w => hq sig G.Hm w (uQ i)) hv2
      simp only [hq_neg_left, hq_smul_l, hxu, mul_zero, neg_zero] at h
      exact h
    rw [hv2, ha, zero_smul, neg_zero]
  let eR : Fin r → G.GLV := fun i => LinearEquiv.ofInjectiveEndo (eQ sig G.Hm (X i) (uQ i) (sQ i)) (hinjQ i)
  have heR : ∀ i v, eR i v = eQ sig G.Hm (X i) (uQ i) (sQ i) v := fun i v => by
    simp only [eR, LinearEquiv.coe_ofInjectiveEndo]
  have hext : ∀ p i, ∃ e' : (G.S p).GLV, A.Ext p (eR i) e' ∧ ∀ v, e' v =
      eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) v := by
    intro p i
    obtain ⟨e', he', -⟩ := (RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 (eR i)
    refine ⟨e', he', fun v => ?_⟩
    let M : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (Fin (k + 2 * r + 1) → (A.loc p).Ep) :=
      { toFun := fun w => eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) w
        map_add' := fun a b => by
          simp only [eich, hf_add_left_flag_measures']
          module
        map_smul' := fun t a => by
          simp only [eich, hf_smul_left_flag_measures', RingHom.id_apply]
          module }
    have hlin := RatExt.lin_ext (A.loc p).ιE (e' : (Fin (k + 2 * r + 1) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] _) M
      (fun x => by
        show e' (A.bc p x) = eich (A.L p) (G.S p).Hm (A.bc p (X i)) (A.bc p (uQ i)) ((A.loc p).ιE (sQ i)) (A.bc p x)
        rw [he' x, heR, bc_eQ, G.Hm_eq p])
    exact LinearMap.congr_fun hlin v
  choose eL heL heL' using hext
  have hmem : ∀ p, (List.ofFn (eL p)).prod ∈ (G.S p).Nof (gF p) := by
    intro p
    refine ((hR p).2.2.2 _).2 ⟨fun i => A.bc p (uQ i), fun i => (A.loc p).ιE (sQ i), eL p,
      fun i => ⟨fun j hj => ?_, ?_, heL' p i⟩, rfl⟩
    · have hj' : j ∈ (Finset.univ.filter fun j : Fin r => j ≤ i) := by simp [hj]
      rw [hform, hform, ((hQ i).1 j hj').1, ((hQ i).1 j hj').2, map_zero]
      exact ⟨rfl, rfl⟩
    · rw [hform, ← (hQ i).2.1, map_add (f := _), hconj]
  refine ⟨(List.ofFn eR).prod, fun p => ⟨_, hmem p, ext_prod A p r eR (eL p) (heL p)⟩, ?_⟩
  intro p g' hg' x hx
  have hg'eq : g' = (List.ofFn (eL p)).prod :=
    ((RatExt.rational_extend A (k + 2 * r + 1) p).2.2.1 ((List.ofFn eR).prod)).unique hg'
      (ext_prod A p r eR (eL p) (heL p))
  rw [hg'eq, hn_eq p]
  exact hd2 p (fun i => A.bc p (uQ i)) (fun i => (A.loc p).ιE (sQ i)) (eL p) (heL' p)
    (fun i j => ((hQ i).2.2 p).1 j) (fun i => ((hQ i).2.2 p).2) x hx

theorem strong_approximation_unipotent : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c hc n hn
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f) (fun p => (G.S p).es)
      (fun a => G.f a.castSucc) G.es (fun _ => Or.inl ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es_eq p a) hN
    exact ⟨g, hg1, hg2⟩
  · obtain ⟨g, hg1, hg2⟩ := core A r k G Λ hΛ c hc n hn (fun p => (G.S p).f') (fun p => (G.S p).es')
      (fun a => G.f' a.castSucc) G.es' (fun _ => Or.inr ⟨rfl, rfl⟩)
      (fun p a => by
        have h := G.f'_eq p a.castSucc
        rwa [Fin.val_castSucc] at h)
      (fun p a => G.es'_eq p a) hN
    exact ⟨g, hg1, hg2⟩

end GlobalTheory.HL.SAN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproximationUnipotentStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strong_approximation_unipotent_alt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, {p | n p • A.lat p Λ ≠ A.lat p Λ}.Finite → ((∀ p, n p ∈ (G.S p).N) → ∃ g ∈ G.N, ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) ∧ ((∀ p, n p ∈ (G.S p).N') → ∃ g ∈ G.N', ∀ p g', A.Ext p g g' → ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y) := by
  exact @_root_.GlobalTheory.HL.SAN.strong_approximation_unipotent
end
