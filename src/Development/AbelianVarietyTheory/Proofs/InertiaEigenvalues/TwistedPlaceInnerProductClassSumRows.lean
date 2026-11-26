module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabMono
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexCj
open GlobalTheory.ClassRefine GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.TwoLattices

open scoped Classical

variable {G : Type} [Group G]

def Reps (Γ H : Subgroup G) (T : Finset G) : Prop :=
  ∀ g : G, ∃! t, t ∈ T ∧ ∃ (γ : Γ) (κ : G), κ ∈ H ∧ g = (γ : G) * t * κ

def Cover (Γ H : Subgroup G) : Prop :=
  ∃ S : Finset G, ∀ g : G, ∃ s ∈ S, ∃ (γ : Γ) (κ : G), κ ∈ H ∧ g = (γ : G) * s * κ

def wsum (Γ H : Subgroup G) (T : Finset G) (Φ : G → ℂ) : ℂ :=
  ∑ t ∈ T, ((Nat.card (stabQ Γ H t) : ℂ))⁻¹ * Φ t

def dsum (Γ H : Subgroup G) (Φ : G → ℂ) : ℂ := if h : ∃ T, Reps Γ H T then wsum Γ H h.choose Φ else 0

def cj (K : Subgroup G) (x : G) : Subgroup G := K.comap (MulAut.conj x⁻¹).toMonoidHom

theorem mem_cj {K : Subgroup G} {x κ : G} : κ ∈ cj K x ↔ x⁻¹ * κ * x ∈ K := by
  simp [cj]

theorem Reps.cover {Γ H : Subgroup G} {T : Finset G} (h : Reps Γ H T) : Cover Γ H :=
  ⟨T, fun g => by obtain ⟨t, ⟨ht, e⟩, -⟩ := h g; exact ⟨t, ht, e⟩⟩

theorem Cover.reps {Γ H : Subgroup G} (h : Cover Γ H) : ∃ T, Reps Γ H T := by
  obtain ⟨S, hS⟩ := h
  let q : G → DoubleCoset.Quotient (Γ : Set G) (H : Set G) := DoubleCoset.mk Γ H
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : Γ) (κ : G), κ ∈ H ∧ b = (γ : G) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (Γ : Set G) (H : Set G), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem Cover.mono {Γ H H' : Subgroup G} (h : Cover Γ H') (hle : H' ≤ H) : Cover Γ H := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, fun g => by obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g; exact ⟨s, hs, γ, κ, hle hκ, e⟩⟩

theorem Cover.of_relIndex {Γ H H' : Subgroup G} (h : Cover Γ H) (hne : H'.relIndex H ≠ 0) : Cover Γ H' := by
  rw [← Subgroup.inf_relIndex_right] at hne
  obtain ⟨U, -, hU, -⟩ := exists_cosetReps (inf_le_right : H' ⊓ H ≤ H) hne
  obtain ⟨S, hS⟩ := h
  refine ⟨(S ×ˢ U).image fun p => p.1 * p.2, fun g => ?_⟩
  obtain ⟨t, ht, γ, κ, hκ, e⟩ := hS g
  obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hU κ hκ
  exact ⟨t * u, Finset.mem_image.2 ⟨(t, u), Finset.mem_product.2 ⟨ht, hu⟩, rfl⟩, γ, u⁻¹ * κ, hu'.1, by rw [e]; group⟩

theorem dsum_eq {Γ H : Subgroup G} {T : Finset G} (hT : Reps Γ H T) {Φ : G → ℂ} (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g)
    (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) : dsum Γ H Φ = wsum Γ H T Φ := by
  have h : ∃ T, Reps Γ H T := ⟨T, hT⟩
  rw [dsum, dite_eq_left h, wsum, sum_classReps_refine le_rfl hT h.choose_spec Φ hl hr (F := {1}) (by simp [H.one_mem])
    (fun κ hκ => ⟨1, by simpa using hκ, fun u hu => by simpa using hu.1⟩)]
  simp [wsum]

theorem dsum_refine {Γ H H' : Subgroup G} (hle : H' ≤ H) (hc : Cover Γ H') {Φ : G → ℂ}
    (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g) (hr : ∀ κ ∈ H', ∀ g, Φ (g * κ) = Φ g) {F : Finset G} (hF : ∀ κ ∈ F, κ ∈ H)
    (hFu : ∀ κ ∈ H, ∃! u, u ∈ F ∧ u⁻¹ * κ ∈ H') : dsum Γ H' Φ = dsum Γ H fun g => ∑ u ∈ F, Φ (g * u) := by
  have h := (hc.mono hle).reps
  have h' := hc.reps
  rw [dsum, dite_eq_left h', dsum, dite_eq_left h, wsum, wsum, sum_classReps_refine hle h.choose_spec h'.choose_spec Φ hl hr hF hFu]

theorem dsum_mul (Γ H : Subgroup G) (c : ℂ) (Φ : G → ℂ) : dsum Γ H (fun g => c * Φ g) = c * dsum Γ H Φ := by
  unfold dsum wsum
  split_ifs
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  · simp

theorem dsum_sum (Γ H : Subgroup G) {ι : Type} (s : Finset ι) (Φ : ι → G → ℂ) :
    dsum Γ H (fun g => ∑ i ∈ s, Φ i g) = ∑ i ∈ s, dsum Γ H (Φ i) := by
  unfold dsum wsum
  split_ifs
  · simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  · simp

theorem dsum_index {Γ H H' : Subgroup G} (hle : H' ≤ H) (hne : H'.relIndex H ≠ 0) (hc : Cover Γ H') {Φ : G → ℂ}
    (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g) (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) :
    dsum Γ H' Φ = (H'.relIndex H : ℂ) * dsum Γ H Φ := by
  obtain ⟨F, h1, h2, h3⟩ := exists_cosetReps hle hne
  rw [dsum_refine hle hc hl (fun κ hκ => hr κ (hle hκ)) h1 h2, ← dsum_mul]
  congr 1
  funext g
  rw [Finset.sum_congr rfl fun u hu => hr u (h1 u hu) g, Finset.sum_const, h3, nsmul_eq_mul]

theorem reps_conj {Γ H : Subgroup G} {T : Finset G} (hT : Reps Γ H T) (δ x : G) :
    Reps (cj Γ δ) (cj H x) (T.image fun t => δ * t * x⁻¹) := by
  intro g
  obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, hu⟩ := hT (δ⁻¹ * g * x)
  refine ⟨δ * t * x⁻¹, ⟨Finset.mem_image_of_mem _ ht, ⟨δ * γ * δ⁻¹, mem_cj.2 (by simp [mul_assoc])⟩, x * κ * x⁻¹,
    mem_cj.2 (by simpa [mul_assoc] using hκ), ?_⟩, ?_⟩
  · have : g = δ * (δ⁻¹ * g * x) * x⁻¹ := by group
    rw [this, e]
    simp [mul_assoc]
  · rintro s ⟨hs, γ', κ', hκ', e'⟩
    obtain ⟨t', ht', rfl⟩ := Finset.mem_image.1 hs
    rw [hu t' ⟨ht', ⟨_, mem_cj.1 γ'.2⟩, _, mem_cj.1 hκ', by rw [e']; simp [mul_assoc]⟩]

def stabConj (Γ H : Subgroup G) (δ x t : G) : stabQ (cj Γ δ) (cj H x) (δ * t * x⁻¹) ≃ stabQ Γ H t where
  toFun γ := ⟨⟨_, mem_cj.1 γ.1.2⟩, mem_stabQ.2 (by simpa [mul_assoc] using mem_cj.1 (mem_stabQ.1 γ.2))⟩
  invFun γ := ⟨⟨δ * γ.1 * δ⁻¹, mem_cj.2 (by simp [mul_assoc])⟩,
    mem_stabQ.2 (mem_cj.2 (by simpa [mul_assoc] using mem_stabQ.1 γ.2))⟩
  left_inv γ := Subtype.ext (Subtype.ext (by simp [mul_assoc]))
  right_inv γ := Subtype.ext (Subtype.ext (by simp [mul_assoc]))

theorem dsum_conj {Γ H : Subgroup G} (hc : Cover Γ H) {Φ : G → ℂ} (hl : ∀ (γ : Γ) g, Φ ((γ : G) * g) = Φ g)
    (hr : ∀ κ ∈ H, ∀ g, Φ (g * κ) = Φ g) (δ x : G) :
    dsum (cj Γ δ) (cj H x) (fun g => Φ (δ⁻¹ * g * x)) = dsum Γ H Φ := by
  obtain ⟨T, hT⟩ := hc.reps
  rw [dsum_eq hT hl hr, dsum_eq (reps_conj hT δ x), wsum, wsum, Finset.sum_image (fun a _ b _ e => by simpa using e)]
  · refine Finset.sum_congr rfl fun t _ => ?_
    rw [Nat.card_congr (stabConj Γ H δ x t)]
    simp [mul_assoc]
  · intro γ g
    rw [← hl ⟨_, mem_cj.1 γ.2⟩ (δ⁻¹ * g * x)]
    simp [mul_assoc]
  · intro κ hκ g
    rw [← hr _ (mem_cj.1 hκ) (δ⁻¹ * g * x)]
    simp [mul_assoc]

theorem cj_one (K : Subgroup G) : cj K 1 = K := by
  ext; simp [mem_cj]

theorem relIndex_cj {K : Subgroup G} (h : ∀ x, (cj K x).relIndex K ≠ 0) (x : G) : K.relIndex (cj K x) ≠ 0 := by
  have := h x⁻¹
  rw [cj, Subgroup.relIndex_comap] at this
  convert this using 2
  ext κ
  rw [mem_cj]
  exact ⟨fun h => ⟨_, h, by simp [mul_assoc]⟩, by rintro ⟨k, hk, rfl⟩; simpa [mul_assoc] using hk⟩

def ind (Δ H : Subgroup G) (x g : G) : ℂ := if ∃ δ ∈ Δ, ∃ κ ∈ H, g = δ * x * κ then 1 else 0

theorem ind_left {Δ H : Subgroup G} {x δ : G} (hδ : δ ∈ Δ) (g : G) : ind Δ H x (δ * g) = ind Δ H x g := by
  unfold ind
  refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨δ⁻¹ * a, Δ.mul_mem (Δ.inv_mem hδ) ha, k, hk, ?_⟩,
    fun ⟨a, ha, k, hk, e⟩ => ⟨δ * a, Δ.mul_mem hδ ha, k, hk, by rw [e]; group⟩⟩ rfl rfl
  rw [mul_assoc, mul_assoc, ← mul_assoc a, ← e]; group

theorem ind_right {Δ H : Subgroup G} {x κ : G} (hκ : κ ∈ H) (g : G) : ind Δ H x (g * κ) = ind Δ H x g := by
  unfold ind
  refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, k * κ⁻¹, H.mul_mem hk (H.inv_mem hκ), ?_⟩,
    fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, k * κ, H.mul_mem hk hκ, by rw [e]; group⟩⟩ rfl rfl
  rw [← mul_assoc, ← e]; group

theorem mass_refine (Δ : Subgroup G) {H H' : Subgroup G} (hle : H' ≤ H) (hne : H'.relIndex H ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ Γ : Subgroup G, Γ ≤ Δ → Cover Γ H' → dsum Γ H' (ind Δ H' 1) = n * dsum Γ H (ind Δ H 1) := by
  obtain ⟨F, h1, h2, -⟩ := exists_cosetReps hle hne
  refine ⟨(F.filter fun u => ∃ δ ∈ Δ, ∃ κ ∈ H', u = δ * 1 * κ).card, ?_, fun Γ hΓ hc => ?_⟩
  · obtain ⟨u, ⟨hu, hu'⟩, -⟩ := h2 1 H.one_mem
    exact Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨hu, 1, Δ.one_mem, u, by simpa using hu', by simp⟩)
  rw [dsum_refine hle hc (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ) h1 h2, ← dsum_mul]
  congr 1
  funext g
  by_cases hg : ∃ δ ∈ Δ, ∃ κ ∈ H, g = δ * 1 * κ
  · obtain ⟨δ, hδ, κ, hκ, rfl⟩ := hg
    have e : ∑ u ∈ F, ind Δ H' 1 (κ * u) = ∑ u ∈ F, ind Δ H' 1 u := by
      choose! r hr hru using fun u (hu : u ∈ H) => h2 u hu
      have hm : ∀ u ∈ F, κ * u ∈ H := fun u hu => H.mul_mem hκ (h1 u hu)
      refine Finset.sum_bij (fun u _ => r (κ * u)) (fun u hu => (hr _ (hm u hu)).1) (fun a ha b hb e => ?_) (fun b hb => ?_)
        (fun u hu => ?_)
      · have h3 := (hr _ (hm a ha)).2
        have h4 := (hr _ (hm b hb)).2
        rw [e] at h3
        have := H'.mul_mem (H'.inv_mem h3) h4
        exact (hru b (h1 b hb) a ⟨ha, by simpa [mul_assoc] using this⟩).trans
          (hru b (h1 b hb) b ⟨hb, by simp [H'.one_mem]⟩).symm
      · have hb' : κ⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hκ) (h1 b hb)
        refine ⟨r (κ⁻¹ * b), (hr _ hb').1, (hru _ (hm _ (hr _ hb').1) b ⟨hb, ?_⟩).symm⟩
        simpa [mul_assoc] using H'.inv_mem (hr _ hb').2
      · rw [← ind_right (hr _ (hm u hu)).2 (r (κ * u))]
        simp
    simp_rw [mul_one, mul_assoc, ind_left hδ]
    rw [e, ← one_mul κ, ind_right hκ]
    simp only [ind]
    rw [if_pos ⟨1, Δ.one_mem, 1, H.one_mem, by simp⟩, Finset.sum_boole, mul_one]
    simp only [mul_one]
  · rw [ind, if_neg hg, mul_zero]
    refine Finset.sum_eq_zero fun u hu => if_neg fun ⟨δ, hδ, κ, hκ, e⟩ => hg ⟨δ, hδ, κ * u⁻¹, H.mul_mem (hle hκ) (H.inv_mem (h1 u hu)), ?_⟩
    rw [← mul_assoc, ← e]; group

theorem mass_pos {Δ Γ H : Subgroup G} (hΓ : Γ ≤ Δ) (hc : Cover Γ H) (hf : ∀ t, Finite (stabQ Γ H t)) :
    ∃ m : ℝ, 0 < m ∧ dsum Γ H (ind Δ H 1) = m := by
  obtain ⟨T, hT⟩ := hc.reps
  refine ⟨∑ t ∈ T, ((Nat.card (stabQ Γ H t) : ℝ))⁻¹ * if ∃ δ ∈ Δ, ∃ κ ∈ H, t = δ * 1 * κ then 1 else 0, ?_, ?_⟩
  · obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT 1
    refine Finset.sum_pos' (fun s _ => by positivity) ⟨t, ht, ?_⟩
    have e' : t = (γ : G)⁻¹ * 1 * κ⁻¹ := by rw [e]; group
    rw [if_pos ⟨(γ : G)⁻¹, Δ.inv_mem (hΓ γ.2), κ⁻¹, H.inv_mem hκ, e'⟩, mul_one]
    haveI := hf t
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  · rw [dsum_eq hT (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ), wsum]
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold ind
    split_ifs <;> simp

theorem dsum_prop {Δ Γ Γ' K : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0) (hΓ : Γ ≤ Δ) (hΓ' : Γ' ≤ Δ)
    (hc : Cover Γ K) (hc' : Cover Γ' K) (hf : ∀ t, Finite (stabQ Γ K t)) (hf' : ∀ t, Finite (stabQ Γ' K t)) :
    ∃ c : ℝ, 0 < c ∧ ∀ Φ : G → ℂ, (∀ δ ∈ Δ, ∀ g, Φ (δ * g) = Φ g) → (∀ κ ∈ K, ∀ g, Φ (g * κ) = Φ g) →
      dsum Γ K Φ = c * dsum Γ' K Φ := by
  obtain ⟨m, hm, em⟩ := mass_pos hΓ hc hf
  obtain ⟨m', hm', em'⟩ := mass_pos hΓ' hc' hf'
  have key : ∀ x, ∃ q : ℂ, ∀ Γ : Subgroup G, Γ ≤ Δ → Cover Γ K → dsum Γ K (ind Δ K x) = q * dsum Γ K (ind Δ K 1) := by
    intro x
    have h1 : (cj K x ⊓ K).relIndex K ≠ 0 := by rw [Subgroup.inf_relIndex_right]; exact hK x
    have h2 : (cj K x ⊓ K).relIndex (cj K x) ≠ 0 := by rw [Subgroup.inf_relIndex_left]; exact relIndex_cj hK x
    obtain ⟨n, -, en⟩ := mass_refine Δ inf_le_right h1
    obtain ⟨n', hn', en'⟩ := mass_refine Δ inf_le_left h2
    refine ⟨n / n', fun Γ hΓ hc => ?_⟩
    have hn'' : (n' : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn'
    rw [div_mul_eq_mul_div, ← en Γ hΓ (hc.of_relIndex h1), en' Γ hΓ (hc.of_relIndex h1), mul_div_cancel_left₀ _ hn'',
      ← dsum_conj hc (fun γ => ind_left (hΓ γ.2)) (fun κ hκ => ind_right hκ) 1 x, cj_one]
    congr 1
    funext g
    unfold ind
    refine if_congr ⟨fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, x * k * x⁻¹, mem_cj.2 (by simpa [mul_assoc] using hk), ?_⟩,
      fun ⟨a, ha, k, hk, e⟩ => ⟨a, ha, _, mem_cj.1 hk, by rw [e]; group⟩⟩ rfl rfl
    have : g = (1⁻¹ * g * x) * x⁻¹ := by group
    rw [this, e]; group
  choose q hq using key
  have hcΔ : Cover Δ K := by
    obtain ⟨S, hS⟩ := hc
    exact ⟨S, fun g => by obtain ⟨s, hs, γ, e⟩ := hS g; exact ⟨s, hs, ⟨γ, hΓ γ.2⟩, e⟩⟩
  obtain ⟨X, hX⟩ := hcΔ.reps
  refine ⟨m / m', div_pos hm hm', fun Φ hl hr => ?_⟩
  have hΦ : Φ = fun g => ∑ x ∈ X, Φ x * ind Δ K x g := by
    funext g
    obtain ⟨x, ⟨hx, δ, κ, hκ, e⟩, hu⟩ := hX g
    rw [Finset.sum_eq_single_of_mem x hx fun y hy hne => ?_]
    · rw [ind, if_pos ⟨δ, δ.2, κ, hκ, e⟩, mul_one, e, hr κ hκ, hl _ δ.2]
    · rw [ind, if_neg fun ⟨a, ha, k, hk, e'⟩ => hne (hu y ⟨hy, ⟨a, ha⟩, k, hk, e'⟩), mul_zero]
  have hm'' : (m' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hm'.ne'
  rw [hΦ, dsum_sum, dsum_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [dsum_mul, dsum_mul, hq x Γ hΓ hc, hq x Γ' hΓ' hc', em, em']
  push_cast
  field_simp

end GlobalTheory.TwoLattices

end
end

open GlobalTheory.ClassRefine GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.TwoLattices

open scoped Classical

variable {G : Type} [Group G]

theorem finite_stab_mono {Γ Γ' K K' : Subgroup G} (h : Γ' ≤ Γ) (hK : K' ≤ K) (t : G) (hf : Finite (stabQ Γ K t)) :
    Finite (stabQ Γ' K' t) :=
  Finite.of_injective (fun γ : stabQ Γ' K' t => (⟨⟨γ.1, h γ.1.2⟩, mem_stabQ.2 (hK (mem_stabQ.1 γ.2))⟩ : stabQ Γ K t))
    fun _ _ e => Subtype.ext (Subtype.ext (congrArg (fun z : stabQ Γ K t => (z.1 : G)) e))

theorem Cover.of_finite {Γ Γ' K : Subgroup G} (hc : Cover Γ K) {α : Type} [Finite α] (r : Γ → α)
    (hr : ∀ a b, r a = r b → (a : G) * (b : G)⁻¹ ∈ Γ') : Cover Γ' K := by
  obtain ⟨S, hS⟩ := hc
  haveI := Fintype.ofFinite α
  refine ⟨(Finset.univ ×ˢ S).image fun p : α × G => ((Function.invFun r p.1 : Γ) : G) * p.2, fun g => ?_⟩
  obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g
  exact ⟨_, Finset.mem_image.2 ⟨(r γ, s), Finset.mem_product.2 ⟨Finset.mem_univ _, hs⟩, rfl⟩,
    ⟨_, hr γ _ (Function.invFun_eq ⟨γ, rfl⟩).symm⟩, κ, hκ, by rw [e]; simp [mul_assoc]⟩

def Kn (G X : Type) : Type := G × G → X → X → ℂ

variable {W X : Type} [AddCommGroup W] [Module ℂ W]

instance : MulAction G (Kn G X) where
  smul δ k := fun p => k (δ⁻¹ * p.1, δ⁻¹ * p.2)
  one_smul k := funext fun p => by
    show k (1⁻¹ * p.1, 1⁻¹ * p.2) = k p
    simp
  mul_smul a b k := funext fun p => by
    show k ((a * b)⁻¹ * p.1, (a * b)⁻¹ * p.2) = k (b⁻¹ * (a⁻¹ * p.1), b⁻¹ * (a⁻¹ * p.2))
    simp [mul_assoc]

theorem smul_kn (δ : G) (k : Kn G X) (p : G × G) : (δ • k) p = k (δ⁻¹ * p.1, δ⁻¹ * p.2) := rfl

def kn (f : X → G → W) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Kn G X := fun p x x' => b (f x p.1) (f x' p.2)

def acts (f : X → G → W) : Subgroup G where
  carrier := {δ | (∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ * g) = A (f x g)) ∧ ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (δ⁻¹ * g) = A (f x g)}
  one_mem' := ⟨⟨LinearMap.id, by simp⟩, ⟨LinearMap.id, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨A, hA⟩, A', hA'⟩ ⟨⟨B, hB⟩, B', hB'⟩
    exact ⟨⟨A.comp B, fun x g => by rw [mul_assoc, hA, hB]; rfl⟩,
      ⟨B'.comp A', fun x g => by rw [mul_inv_rev, mul_assoc, hB', hA']; rfl⟩⟩
  inv_mem' := by
    rintro a ⟨h, h'⟩
    exact ⟨h', by simpa using h⟩

theorem le_acts {f : X → G → W} {Γ : Subgroup G} (h : ∀ γ ∈ Γ, ∃ A : W →ₗ[ℂ] W, ∀ x g, f x (γ * g) = A (f x g)) : Γ ≤ acts f :=
  fun γ hγ => ⟨h γ hγ, h _ (Γ.inv_mem hγ)⟩

def IsPos (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : Prop := (∀ x y, b x y = starRingEnd ℂ (b y x)) ∧ ∀ x, x ≠ 0 → 0 < (b x x).re

section Span

variable {f : X → G → W} {ι : Type} {p : ι → X × G} (hs : Submodule.span ℂ (Set.range fun i => f (p i).1 (p i).2) = ⊤)
include hs

theorem smul_kn_pos {δ : G} (hδ : δ ∈ acts f) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) : ∃ b', IsPos b' ∧ kn f b' = δ • kn f b := by
  obtain ⟨⟨A, hA⟩, A', hA'⟩ := hδ
  have h : A.comp A' = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [LinearMap.comp_apply, ← hA', ← hA]
    simp
  refine ⟨(b.comp A').compl₂ A', ⟨fun x y => hb.1 _ _, fun x hx => hb.2 _ fun h0 => hx ?_⟩, funext fun q => ?_⟩
  · have := LinearMap.congr_fun h x
    rw [LinearMap.comp_apply, h0, map_zero] at this
    exact this.symm
  · funext x x'
    show b (A' _) (A' _) = b _ _
    rw [hA', hA']

theorem fix_of_mem {K : Subgroup G} (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) {δ : G} (hδ : δ ∈ acts f)
    (h : ∀ i, δ ∈ cj K (p i).2) (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) : δ • kn f b = kn f b := by
  obtain ⟨-, A, hA⟩ := hδ
  have e : A = LinearMap.id := LinearMap.ext_on_range hs fun i => by
    rw [← hA, LinearMap.id_apply, ← hr _ (mem_cj.1 (h i))]
    simp [mul_assoc]
  funext q x x'
  show b _ _ = b _ _
  rw [hA, hA, e]
  rfl

theorem finite_orbit [Finite ι] {K Γ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0) (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g)
    (hΓ : Γ ≤ acts f) (hc : Cover Γ K) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b) (hinv : ∀ γ ∈ Γ, γ • kn f b = kn f b) :
    Finite (MulAction.orbit (acts f) (kn f b)) := by
  obtain ⟨S, hS⟩ := hc.of_relIndex (Subgroup.relIndex_iInf_ne_zero fun i => hK (p i).2)
  choose s hs' γ κ hκ e using hS
  choose δ hδ using fun k : MulAction.orbit (acts f) (kn f b) => k.2
  refine Finite.of_injective (fun k => (⟨s (δ k : G)⁻¹, hs' _⟩ : S)) fun k k' h => Subtype.ext ?_
  have h1 : s (δ k : G)⁻¹ = s (δ k' : G)⁻¹ := congrArg Subtype.val h
  have h2 := e (δ k : G)⁻¹
  have h3 := e (δ k' : G)⁻¹
  rw [h1] at h2
  rw [← hδ k, ← hδ k']
  generalize γ (δ k : G)⁻¹ = a at h2
  generalize γ (δ k' : G)⁻¹ = a' at h3
  have h4 := hκ (δ k : G)⁻¹
  have h5 := hκ (δ k' : G)⁻¹
  generalize κ (δ k : G)⁻¹ = c at h2 h4
  generalize κ (δ k' : G)⁻¹ = c' at h3 h5
  generalize s (δ k' : G)⁻¹ = t at h2 h3
  have h6 : c⁻¹ * c' = δ k * (a * (a' : G)⁻¹) * (δ k' : G)⁻¹ := by
    rw [h3, inv_eq_iff_eq_inv.1 h2]; group
  have h7 : (δ k : G) = c⁻¹ * c' * δ k' * (a' * (a : G)⁻¹) := by rw [h6]; group
  obtain ⟨b', -, hb'⟩ := smul_kn_pos hs (δ k').2 hb
  show (δ k : G) • kn f b = (δ k' : G) • kn f b
  rw [h7, mul_smul, mul_smul, hinv _ (Γ.mul_mem a'.2 (Γ.inv_mem a.2)), ← hb']
  refine fix_of_mem hs hr ?_ (fun i => Subgroup.mem_iInf.1 (Subgroup.mul_mem _ (Subgroup.inv_mem _ h4) h5) i) b'
  rw [h6]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (δ k).2 (hΓ (Γ.mul_mem a.2 (Γ.inv_mem a'.2)))) (Subgroup.inv_mem _ (δ k').2)

theorem exists_form [Finite ι] {K Γ₁ Γ₂ : Subgroup G} (hK : ∀ x, (cj K x).relIndex K ≠ 0)
    (hr : ∀ κ ∈ K, ∀ x g, f x (g * κ) = f x g) (h₁ : Γ₁ ≤ acts f) (h₂ : Γ₂ ≤ acts f) (hc₁ : Cover Γ₁ K) (hc₂ : Cover Γ₂ K)
    (hf₁ : ∀ t, Finite (stabQ Γ₁ K t)) (hf₂ : ∀ t, Finite (stabQ Γ₂ K t)) {b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ} (hb : IsPos b)
    (hinv : ∀ γ ∈ Γ₂, ∀ x x' g g', b (f x (γ * g)) (f x' (γ * g')) = b (f x g) (f x' g')) :
    ∃ (β : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (c : ℝ), IsPos β ∧ 0 < c ∧
      (∀ γ ∈ Γ₁, ∀ x x' g g', β (f x (γ * g)) (f x' (γ * g')) = β (f x g) (f x' g')) ∧
      ∀ x x', dsum Γ₂ K (fun g => b (f x g) (f x' g)) = c * dsum Γ₁ K fun g => β (f x g) (f x' g) := by
  have hinv' : ∀ γ ∈ Γ₂, γ • kn f b = kn f b := fun γ hγ => funext fun q => funext fun x => funext fun x' =>
    hinv _ (Γ₂.inv_mem hγ) x x' q.1 q.2
  haveI := finite_orbit hs hK hr h₂ hc₂ hb hinv'
  set O := MulAction.orbit (acts f) (kn f b) with hO
  haveI := Fintype.ofFinite O
  have hk₀ : kn f b ∈ O := MulAction.mem_orbit_self _
  choose δ hδ using fun k : O => k.2
  choose B hB eB using fun k : O => smul_kn_pos hs (δ k).2 hb
  have eB' : ∀ k, kn f (B k) = k := fun k => (eB k).trans (hδ k)
  have hβ : ∀ x x' g g', (∑ k, B k) (f x g) (f x' g') = ∑ k : O, (k : Kn G X) (g, g') x x' := fun x x' g g' => by
    rw [LinearMap.sum_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [← eB' k]; rfl
  have hβinv : ∀ γ ∈ acts f, ∀ x x' g g', (∑ k, B k) (f x (γ * g)) (f x' (γ * g')) = (∑ k, B k) (f x g) (f x' g') := by
    intro γ hγ x x' g g'
    rw [hβ, hβ, ← Equiv.sum_comp (MulAction.toPerm (⟨γ, hγ⟩ : acts f))]
    refine Finset.sum_congr rfl fun k _ => ?_
    show (γ • (k : Kn G X)) (γ * g, γ * g') x x' = _
    simp [smul_kn]
  let Δ : Subgroup G := fixingSubgroup G O
  have hΔ : ∀ a, a ∈ Δ ↔ ∀ k ∈ O, a • k = k := fun a => mem_fixingSubgroup_iff G
  have hst : ∀ a ∈ acts f, ∀ k ∈ O, a • k ∈ O := fun a ha k hk => (((⟨a, ha⟩ : acts f) • (⟨k, hk⟩ : O) : O)).2
  have hc₃ : Cover (Γ₂ ⊓ Δ) K := hc₂.of_finite (fun γ (k : O) => (⟨(γ : G)⁻¹ • (k : Kn G X), hst _ (h₂ (Γ₂.inv_mem γ.2)) _ k.2⟩ : O))
    fun a a' e => ⟨Γ₂.mul_mem a.2 (Γ₂.inv_mem a'.2), (hΔ _).2 fun k hk => by
      have : (a : G)⁻¹ • k = (a' : G)⁻¹ • k := congrArg Subtype.val (congrFun e ⟨k, hk⟩)
      rw [mul_smul, ← this, smul_inv_smul]⟩
  have hf₃ : ∀ t, Finite (stabQ (Γ₂ ⊓ Δ) K t) := fun t => finite_stab_mono inf_le_left le_rfl t (hf₂ t)
  have hl₀ : ∀ x x', ∀ γ ∈ Γ₂, ∀ g, b (f x (γ * g)) (f x' (γ * g)) = b (f x g) (f x' g) := fun x x' γ hγ g => hinv γ hγ x x' g g
  have hr₀ : ∀ (b : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) x x', ∀ κ ∈ K, ∀ g, b (f x (g * κ)) (f x' (g * κ)) = b (f x g) (f x' g) :=
    fun b x x' κ hκ g => by rw [hr κ hκ, hr κ hκ]
  have hk : ∀ k : O, ∃ c : ℝ, 0 < c ∧ ∀ x x', dsum (Γ₂ ⊓ Δ) K (fun g => (k : Kn G X) (g, g) x x') =
      c * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
    intro k
    obtain ⟨T, hT⟩ := hc₃.reps
    have hc₄ := (reps_conj hT (δ k) 1).cover
    rw [cj_one] at hc₄
    obtain ⟨c, hc, e⟩ := dsum_prop (Δ := Δ) hK inf_le_right (fun a ha => (hΔ _).2 fun k' hk' => by
        have := (hΔ _).1 (mem_cj.1 ha).2 _ (hst _ (Subgroup.inv_mem _ (δ k).2) _ hk')
        rw [mul_smul, smul_inv_smul, mul_smul] at this
        exact smul_left_cancel _ this) hc₃ hc₄ hf₃ (fun t => by
        have := (stabConj (Γ₂ ⊓ Δ) K (δ k) 1 ((δ k : G)⁻¹ * t)).finite_iff.2 (hf₃ _)
        rwa [cj_one, inv_one, mul_one, mul_inv_cancel_left] at this)
    refine ⟨c, hc, fun x x' => ?_⟩
    rw [e _ (fun a ha g => ?_) (fun κ hκ g => ?_), ← dsum_conj hc₃ (fun γ => hl₀ x x' γ γ.2.1) (hr₀ b x x') (δ k) 1, cj_one]
    · congr 2
      funext g
      rw [← hδ k, mul_one]
      rfl
    · conv_rhs => rw [← (hΔ _).1 (Δ.inv_mem ha) k k.2]
      simp [smul_kn]
    · rw [← eB' k]
      exact hr₀ _ x x' κ hκ g
  choose c hc ec using hk
  obtain ⟨c₁, hc₁', e₁⟩ := dsum_prop hK (inf_le_left.trans h₂) h₁ hc₃ hc₁ hf₃ hf₁
  obtain ⟨c₂, hc₂', e₂⟩ := dsum_prop hK le_rfl inf_le_left hc₂ hc₃ hf₂ hf₃
  have hpos : 0 < ∑ k, c k := Finset.sum_pos (fun k _ => hc k) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  refine ⟨∑ k, B k, c₂ * c₁ / ∑ k, c k, ⟨fun x y => ?_, fun x hx => ?_⟩, by positivity, fun γ hγ => hβinv γ (h₁ hγ), fun x x' => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [LinearMap.sum_apply, map_sum]
      exact Finset.sum_congr rfl fun k _ => (hB k).1 x y
  · simp only [LinearMap.sum_apply, Complex.re_sum]
    exact Finset.sum_pos (fun k _ => (hB k).2 x hx) ⟨⟨_, hk₀⟩, Finset.mem_univ _⟩
  · have e₃ := e₁ (fun g => (∑ k, B k) (f x g) (f x' g)) (fun a ha g => hβinv a ha x x' g g) (hr₀ _ x x')
    have e₄ : dsum (Γ₂ ⊓ Δ) K (fun g => (∑ k, B k) (f x g) (f x' g)) =
        ((∑ k, c k : ℝ) : ℂ) * dsum (Γ₂ ⊓ Δ) K fun g => b (f x g) (f x' g) := by
      simp_rw [hβ]
      rw [dsum_sum, Complex.ofReal_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => ec k x x'
    have hne : ((∑ k, c k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hpos.ne'
    rw [e₂ _ (hl₀ x x') (hr₀ b x x'), Complex.ofReal_div, Complex.ofReal_mul, div_mul_eq_mul_div, mul_assoc, ← e₃, e₄]
    field_simp

end Span

end GlobalTheory.TwoLattices

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.TwoLattices GlobalTheory.ClassRefine GlobalTheory.ClassPet
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FormInner

theorem wsum_transport {A G Γ W I : Type} [Group A] [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : A ≃* G) (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, Reps (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) T ∧ ∀ F F' : G → W,
      wsum (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) T (fun g => inner ℂ (F (φ g)) (F' (φ g))) =
        Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : ι.range.comap φ.toMonoidHom) (κ : A), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : A) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun F F' => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [wsum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), ⟨δ, by simp⟩⟩, mem_stabQ.2 (by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2)⟩ :
        stabQ (ι.range.comap φ.toMonoidHom) (J.comap φ.toMonoidHom) (φ.symm (y i)))) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : A)) e)))
    · obtain ⟨δ, hδ⟩ := γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using mem_stabQ.1 γ.2

section Std

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem relIndex_ne_zero_of_cover' {G : Type} [Group G] {H K : Subgroup G} (F : Finset G) (hF : ∀ κ ∈ K, ∃ f ∈ F, f⁻¹ * κ ∈ H) :
    H.relIndex K ≠ 0 := by
  classical
  have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ K, f₀⁻¹ * κ ∈ H) → u ∈ K ∧ f₀⁻¹ * u ∈ H := fun f₀ _ => by
    by_cases h : ∃ κ ∈ K, f₀⁻¹ * κ ∈ H
    · obtain ⟨u, hu⟩ := h
      exact ⟨u, fun _ => hu⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose! u hu using this
  rw [← Subgroup.inf_relIndex_right]
  refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) inf_le_right
  obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
  obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
  refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, ?_, K.mul_mem (K.inv_mem h2) hκ⟩
  have := H.mul_mem (H.inv_mem h3) h₁
  simpa [mul_assoc] using this

theorem bounded_of_le {J : Subgroup (GAf L n)} (h : J ≤ ReciprocityTheory.Aut.Umax L n) : IsBounded J :=
  ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using h hκ⟩⟩

theorem congSub_relIndex {J : Subgroup (GAf L n)} (hJ : IsBounded J) {N : ℕ} (hN : 0 < N) : (congSub L n N).relIndex J ≠ 0 := by
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  exact relIndex_ne_zero_of_cover' F hF

theorem relIndex_of_le {G : Type} [Group G] {H H' K : Subgroup G} (h : H ≤ H') (hne : H.relIndex K ≠ 0) : H'.relIndex K ≠ 0 :=
  fun h0 => hne (Subgroup.relIndex_eq_zero_of_le_left h h0)

theorem relIndex_of_le' {G : Type} [Group G] {H K K' : Subgroup G} (h : K' ≤ K) (hne : H.relIndex K ≠ 0) : H.relIndex K' ≠ 0 :=
  fun h0 => hne (Subgroup.relIndex_eq_zero_of_le_right h h0)

theorem cj_relIndex {K : Subgroup (GAf L n)} (hle : K ≤ ReciprocityTheory.Aut.Umax L n) (hne : K.relIndex (ReciprocityTheory.Aut.Umax L n) ≠ 0) (x) :
    (TwoLattices.cj K x).relIndex K ≠ 0 := by
  obtain ⟨N, hN, h⟩ := (GlobalTheory.CongIndex.finite_index_conj L n _ (bounded_of_le le_rfl) x 1 one_pos).1
  have h1 : (TwoLattices.cj (ReciprocityTheory.Aut.Umax L n) x).relIndex (ReciprocityTheory.Aut.Umax L n) ≠ 0 :=
    relIndex_of_le (fun κ hκ => mem_cj.2 (h κ hκ).1) (congSub_relIndex (bounded_of_le le_rfl) hN)
  have h2 : (TwoLattices.cj K x).relIndex (TwoLattices.cj (ReciprocityTheory.Aut.Umax L n) x) ≠ 0 := by
    rw [TwoLattices.cj, TwoLattices.cj, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective (MulAut.conj x⁻¹).surjective]
    exact hne
  exact relIndex_of_le' hle (Subgroup.relIndex_ne_zero_trans h2 h1)

theorem cover_umax : Cover (ReciprocityTheory.Aut.GQ L n) (ReciprocityTheory.Aut.Umax L n) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ClassFinConj.exists_finset_double_cosets_conj L n 1
  exact ⟨T, fun g => by obtain ⟨γ, hγ, t, ht, κ, hκ, e⟩ := hT g; exact ⟨t, ht, ⟨γ, hγ⟩, κ, hκ.1, e⟩⟩

theorem finite_stabQ {J : Subgroup (GAf L n)} (hJ : IsBounded J) (t) : Finite (stabQ (ReciprocityTheory.Aut.GQ L n) J t) :=
  (Equiv.subtypeEquivRight fun _ => mem_stabQ).finite_iff.2 (GlobalTheory.StabFin.finite_conj_mem L n J hJ t)

theorem relIndex_of_cover {G : Type} [Group G] {Γ K U : Subgroup G} (hle : K ≤ U) (hc : Cover Γ K)
    (hf : ∀ t, Finite (stabQ Γ U t)) : K.relIndex U ≠ 0 := by
  obtain ⟨S, hS⟩ := hc
  refine (GlobalTheory.UnimodMass.mass_eq_relIndex_mul Γ K U hle (GlobalTheory.UnimodMass.finite_dc_of_cover ⟨S, fun g => ?_⟩)
    fun t => (Equiv.subtypeEquivRight fun _ => mem_stabQ).finite_iff.1 (hf t)).1
  obtain ⟨s, hs, γ, κ, hκ, e⟩ := hS g
  exact ⟨γ, γ.2, s, hs, κ, hκ, e⟩

theorem classSum_eq_wsum (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (J : Subgroup (GAf L n)) (T : Finset (GAf L n))
    (f f' : GAf L n → a.W) : classSum a β J T f f' = wsum (ReciprocityTheory.Aut.GQ L n) J T fun g => β (f g) (f' g) := by
  simp only [classSum, wsum, card_stabQ_eq]

theorem span_values (a : NG.AlgWt L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) (h₀ : f ≠ 0) :
    Submodule.span ℂ (Set.range f) = ⊤ := by
  let U : Subrepresentation a.ρ := ⟨Submodule.span ℂ (Set.range f), fun g w hw => by
    refine Submodule.span_induction (p := fun w _ => a.ρ g w ∈ Submodule.span ℂ (Set.range f)) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, hf.1 g h⟩
    · simp
    · intro a b _ _ ha hb
      rw [map_add]; exact add_mem ha hb
    · intro c a _ ha
      rw [map_smul]; exact Submodule.smul_mem _ c ha⟩
  have hU : U = ⊤ := by
    haveI := a.irr
    refine (eq_bot_or_eq_top U).resolve_left fun hb => h₀ ?_
    funext g
    have : f g ∈ U.toSubmodule := Submodule.subset_span ⟨g, rfl⟩
    rw [hb] at this
    exact this
  exact congrArg Subrepresentation.toSubmodule hU

theorem span_finite_values (a : NG.AlgWt L n) {f : GAf L n → a.W} (hf : f ∈ NG.AFall L n a.ρ) (h₀ : f ≠ 0) :
    ∃ (m : ℕ) (g : Fin m → GAf L n), Submodule.span ℂ (Set.range fun i => f (g i)) = ⊤ := by
  obtain ⟨_, ι, _, _, b, -⟩ := a.alg
  haveI : Module.Finite ℂ a.W := Module.Finite.of_basis b
  have h := span_values a hf h₀
  obtain ⟨s, hs, hsp, hli⟩ := exists_linearIndependent ℂ (Set.range f)
  haveI : Finite s := hli.finite
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  choose g hg using fun v : s => hs v.2
  refine ⟨m, fun i => g (e.symm i), ?_⟩
  rw [← h, ← hsp]
  congr 1
  ext v
  exact ⟨by rintro ⟨i, rfl⟩; simp only [hg]; exact (e.symm i).2, fun hv => ⟨e ⟨v, hv⟩, by simp [hg]⟩⟩

end Std

variable {D : D7} {μ : D.what₂.Tup} {j : ℕ} (X : MtReal D μ j) {G Γ W : Type} [Group G] [Group Γ] [NormedAddCommGroup W]
  [InnerProductSpace ℂ W] (ι : Γ →* G) (φ : GAf D.host.E D.R.nV ≃* G) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ)
  (e : X.wt.W ≃ₗ[ℂ] W) (Fm : D.what₂.Mt μ j → G → W)

theorem classSum_of_frame {I : Type} [Fintype I] (y : I → G) (hy : Bridge.IsReps ι J y) (hι : Function.Injective ι)
    (hfin : ∀ t, Finite (stabQ (ι.range.comap φ.toMonoidHom) (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) t))
    (hρ : ∀ δ (a b : W), inner ℂ (ρ δ a) (ρ δ b) = inner ℂ a b)
    (hJ : J.comap φ.toMonoidHom ≤ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) (hX : IsBounded X.J)
    (hFm : ∀ x, Fm x ∈ Bridge.AdForms ι ρ J χ) (hread : ∀ x g, e (X.real x g) = Fm x (φ g))
    (c : ℝ) (hc : 0 < c) (hip : ∀ x x' : D.what₂.Mt μ j, inner ℂ x x' = (c : ℂ) * Bridge.adInner ι J y (Fm x) (Fm x')) :
    ClassSum X := by
  have hA : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ X.J X.χ := fun x => X.real_range ▸ LinearMap.mem_range_self _ x
  obtain ⟨N, hN, hNJ⟩ := X.J_open
  obtain ⟨T', hT', htr⟩ := wsum_transport (W := W) ι hι φ J y hy
  set Γ₂ := ι.range.comap φ.toMonoidHom with hΓ₂
  set J₂ := J.comap φ.toMonoidHom with hJ₂
  have hNU := congSub_relIndex (bounded_of_le (le_refl (ReciprocityTheory.Aut.Umax D.host.E D.R.nV))) hN
  have hJU : J₂.relIndex (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ≠ 0 := relIndex_of_cover hJ hT'.cover hfin
  set K := congSub D.host.E D.R.nV N ⊓ J₂ with hK
  have hKU : K.relIndex (ReciprocityTheory.Aut.Umax D.host.E D.R.nV) ≠ 0 := Subgroup.relIndex_inf_ne_zero hNU hJU
  have hKle : K ≤ ReciprocityTheory.Aut.Umax D.host.E D.R.nV := inf_le_right.trans hJ
  have hKJ : K ≤ X.J := fun κ hκ => (hNJ κ hκ.1).1
  have hc₁ : Cover (ReciprocityTheory.Aut.GQ D.host.E D.R.nV) K := cover_umax.of_relIndex hKU
  have hK₁ : K.relIndex X.J ≠ 0 := relIndex_of_cover hKJ hc₁ (finite_stabQ hX)
  have hK₂ : K.relIndex J₂ ≠ 0 := relIndex_of_le' hJ hKU
  have hc₂ : Cover Γ₂ K := hT'.cover.of_relIndex hK₂
  obtain ⟨T, hT⟩ := (hc₁.mono hKJ).reps
  refine ⟨hX, ?_⟩
  by_cases hz : ∀ x : D.what₂.Mt μ j, x = 0
  · obtain ⟨β, hβ⟩ := GlobalTheory.InvFormBdd.exists_isInvForm _ _ X.wt
    refine ⟨β, T, 1, hβ, hT, one_pos, fun x x' => ?_⟩
    rw [hz x]
    simp [classSum]
  obtain ⟨x₀, h₀⟩ := not_forall.1 hz
  obtain ⟨m, g, hg⟩ := span_finite_values X.wt (hA x₀).1 fun h => h₀ (X.real_inj (by rw [h, map_zero]))
  have hl₂ : ∀ δ γ, ι δ = φ γ → ∀ x g, e (X.real x (γ * g)) = ρ δ (e (X.real x g)) := fun δ γ h x g => by
    have := hFm x δ (φ g) 1
    rw [hread, hread, map_mul, ← h]
    simpa using this
  have hinv : ∀ γ ∈ Γ₂, ∀ x x' g g', pullForm X e (X.real x (γ * g)) (X.real x' (γ * g')) =
      pullForm X e (X.real x g) (X.real x' g') := by
    rintro γ ⟨δ, hδ⟩ x x' g g'
    rw [pullForm_apply, pullForm_apply, hl₂ δ γ hδ, hl₂ δ γ hδ, hρ]
  obtain ⟨β, c', hβ, hc', hβ₁, hsum⟩ := exists_form (f := fun x => X.real x) (p := fun i => (x₀, g i)) hg
    (cj_relIndex hKle hKU) (fun κ hκ x g => by
      obtain ⟨h1, h2⟩ := hNJ κ hκ.1
      have := congrFun ((hA x).2 ⟨κ, h1⟩) g
      rw [h2, Units.val_one, one_smul] at this
      exact this)
    (le_acts fun γ hγ => ⟨X.wt.ρ ⟨γ, hγ⟩, fun x g => (hA x).1.1 ⟨γ, hγ⟩ g⟩)
    (le_acts (Γ := Γ₂) fun γ ⟨δ, hδ⟩ => ⟨e.symm.toLinearMap ∘ₗ ρ δ ∘ₗ e.toLinearMap, fun x g => e.injective (by
      rw [hl₂ δ γ hδ]; simp)⟩)
    hc₁ hc₂ (finite_stabQ (bounded_of_le hKle)) (fun t => finite_stab_mono le_rfl hKle t (hfin t)) (b := pullForm X e)
    ⟨fun a b => by rw [pullForm_apply, pullForm_apply, inner_conj_symm], fun a ha => by
      rw [pullForm_apply]
      exact (re_inner_self_pos (𝕜 := ℂ) (x := e a)).2 (fun h => ha (e.map_eq_zero_iff.1 h))⟩ hinv
  have hβ' : IsInvForm X.wt β := by
    refine ⟨hβ.1, hβ.2, fun γ a b => ?_⟩
    have : (β.comp (X.wt.ρ γ)).compl₂ (X.wt.ρ γ) = β := LinearMap.ext_on_range hg fun i => LinearMap.ext_on_range hg fun k => by
      show β (X.wt.ρ γ _) (X.wt.ρ γ _) = _
      rw [← (hA x₀).1.1, ← (hA x₀).1.1]
      exact hβ₁ γ γ.2 x₀ x₀ _ _
    exact LinearMap.congr_fun₂ this a b
  have hB : ∀ x, X.real x ∈ NG.TypeSp X.wt.ρ J₂ (χ.comp (φ.toMonoidHom.subgroupComap J)) := fun x =>
    ⟨(hA x).1, fun κ => funext fun g => e.injective (by
      have := hFm x 1 (φ g) ⟨φ κ, κ.2⟩
      show e (X.real x (g * κ)) = e (((χ ⟨φ κ, κ.2⟩ : ℂˣ) : ℂ) • X.real x g)
      rw [map_smul, hread, hread, map_mul]
      simpa using this)⟩
  have p₁ : (0 : ℝ) < K.relIndex X.J := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK₁)
  have p₂ : (0 : ℝ) < K.relIndex J₂ := Nat.cast_pos.2 (Nat.pos_of_ne_zero hK₂)
  refine ⟨β, T, c * (c' * K.relIndex X.J / K.relIndex J₂), hβ', hT, by positivity, fun x x' => ?_⟩
  have r₁ := form_inv β hX (hA x) (hA x')
  have r₂ := form_inv (pullForm X e) (bounded_of_le hJ) (hB x) (hB x')
  have l₁ : ∀ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) g, β (X.real x (γ * g)) (X.real x' (γ * g)) = β (X.real x g) (X.real x' g) :=
    fun γ g => hβ₁ γ γ.2 x x' g g
  have l₂ : ∀ (γ : Γ₂) g, pullForm X e (X.real x (γ * g)) (X.real x' (γ * g)) = pullForm X e (X.real x g) (X.real x' g) :=
    fun γ g => hinv γ γ.2 x x' g g
  have e₀ := hsum x x'
  rw [dsum_index inf_le_right hK₂ hc₂ l₂ r₂, dsum_index hKJ hK₁ hc₁ l₁ r₁, dsum_eq hT' l₂ r₂, dsum_eq hT l₁ r₁] at e₀
  simp only [pullForm_apply, hread] at e₀
  have n₂ : ((K.relIndex J₂ : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hK₂
  rw [hip, ← htr, classSum_eq_wsum, eq_div_of_mul_eq n₂ ((mul_comm _ _).trans e₀)]
  push_cast
  ring

theorem finite_stab_frame {V : HSp D} {n : ℕ} (hV : GlobalTheory.StdFrame.OrthFrame V) {hF : D.host.F = maximalRealSubfield D.host.E}
    {P : principalLevelFrame.RowPsi V n} (hP : GlobalTheory.Mem.R3.StdFrame hF P) (t) :
    Finite (stabQ ((Bridge.ratF V).range.comap (frameEquiv P).toMonoidHom) (ReciprocityTheory.Aut.Umax D.host.E n) t) := by
  let P₀ := GlobalTheory.StdFrameModel.unitPsi hV.gram_eq
  have h₀ := (GlobalTheory.StdFrameModel.stdPsi_unitPsi hV).2
  have hrat : RatFrame P₀ := fun g => by simpa using GlobalTheory.NJoin.Inh.rat_unit hV.gram_eq g
  let θ := (frameEquiv P).trans (frameEquiv P₀).symm
  have hθ : ∀ κ, frameEquiv P₀ (θ κ) = frameEquiv P κ := fun κ => (frameEquiv P₀).apply_symm_apply _
  have hU : ∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E n, θ κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank := fun κ hκ => by
    rw [h₀, TopMult.lift_unique (P₀.into (θ κ)) (P.into κ) (hθ κ)]
    exact (hP.2 κ).1 hκ
  haveI := finite_stabQ (bounded_of_le (le_refl (ReciprocityTheory.Aut.Umax D.host.E V.rank))) (θ t)
  refine Finite.of_injective (β := stabQ (ReciprocityTheory.Aut.GQ D.host.E V.rank) (ReciprocityTheory.Aut.Umax D.host.E V.rank) (θ t))
    (fun γ => ⟨⟨θ γ.1, (hrat.iff _).2 (by rw [hθ]; exact γ.1.2)⟩, mem_stabQ.2 (by simpa using hU _ (mem_stabQ.1 γ.2))⟩)
    fun a b h => Subtype.ext (Subtype.ext (θ.injective (congrArg (fun z => (z.1 : GAf D.host.E V.rank)) h)))

end GlobalTheory.FormInner

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.FormInner

theorem ipVia_apply {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · rw [he h.1.choose_spec, he h.2.choose_spec]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem classSum_of_ad (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_read (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (RatFrame.iff (hrat i)) (fun δ a b => hcV.2.1 _ a b)
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using comap_le_Umax (ad.std i) (hB i) (R.datVt i t) hκ⟩⟩ hX hFm
    hread _ hnP hip (fun _ => GlobalTheory.InvFormBdd.exists_isInvForm _ _ _)

theorem classSum_of_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_frame (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (finite_stab_frame (hV i) (ad.std i)) (fun δ a b => hcV.2.1 _ a b)
    (comap_le_Umax (ad.std i) (hB i) (R.datVt i t)) hX hFm
    hread _ hnP hip

theorem classSum_twisted_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_std Y hM hB ad hV _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

end Gen

theorem orthFrame_of_vStd {D : D7} (i : Fin D.R.m) (h : Formalism.IndefR.FWT.VStd D i) : GlobalTheory.StdFrame.OrthFrame (Vc D i) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.StdFrameCounterexample.vstd_iff i).1 h
  refine ⟨fun a b => (congrFun (congrFun h1 a) b).trans Matrix.one_apply, fun a => ?_⟩
  have := (h2 (Pi.single a 1)).2 fun b => by
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  simpa [Pi.single_apply] using this

theorem sumTw_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f T hO _ w _ Z Wt hX z p0 Y _ _ _ _ _ M tup Q a hin v hv j h1 h2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  obtain ⟨hB, hM⟩ : (∀ i, Formalism.IndefR.Lev.IsBaseFrame (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (z.R.βV i) (z.R.ΛV i) 1) ∧
      z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted_std Y hM hB a (fun i => orthFrame_of_vStd i (hV i)) hin v j h1 h2 hv

end GlobalTheory.FormInner

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRowsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedPlace_innerProduct_classSum_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  first | exact @GlobalTheory.FormInner.sumTw_rows | exact GlobalTheory.FormInner.sumTw_rows | (intros; apply GlobalTheory.FormInner.sumTw_rows <;> assumption)
end
