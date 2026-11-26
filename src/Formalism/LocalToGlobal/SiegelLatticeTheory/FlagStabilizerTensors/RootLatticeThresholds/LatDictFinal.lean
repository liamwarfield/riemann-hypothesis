module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDict
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfG
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZOrbitOfOpen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlueA
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.WuDefiniteHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPfZ
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPlane
noncomputable section

open NumberField

namespace Formalism.L2.SG.Pf.LatDictZ.Z2

open ReciprocityTheory.ChartRestriction.L3.WA

section Generic

variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]

def IdealLike (S : Subring K) (P : K → Prop) : Prop :=
  (∀ a b, P a → P b → P (a - b)) ∧ (∀ x ∈ S, ∀ a, P a → P (x * a)) ∧ ¬ P 1

theorem IdealLike.add {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {a b : K} (ha : P a)
    (hb : P b) : P (a + b) := by
  have := hP.1 a _ ha (hP.2.1 (-1) (S.neg_mem S.one_mem) b hb)
  convert this using 1
  ring

theorem IdealLike.cancel {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {μ a : K}
    (hμ : IsUnitIn S μ) (h : P (μ * a)) : P a := by
  have := hP.2.1 _ hμ.2.2 _ h
  rwa [← mul_assoc, inv_mul_cancel₀ hμ.1, one_mul] at this

theorem IdealLike.not_one_add {S : Subring K} {P : K → Prop} (hP : IdealLike S P) {ε η : K}
    (hε : P ε) (hη : P η) {x y : K} (hx : x ∈ S) (hy : y ∈ S) {v : K} (hv : v = 1 + x * ε + y * η) :
    ¬ P v := by
  intro h
  apply hP.2.2
  have := hP.1 _ _ h (hP.add (hP.2.1 x hx ε hε) (hP.2.1 y hy η hη))
  convert this using 1
  rw [hv]
  ring

theorem plane_ring_half {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) (hPε : P ε) (hPη : P η) :
    IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
      IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η) := by
  have hμS := hμ.2.1
  have hγS : γ ∈ S := by
    have e : γ = 1 - α * ε - β * η := by linear_combination hγ
    rw [e]
    exact S.sub_mem (S.sub_mem S.one_mem (S.mul_mem hα hε)) (S.mul_mem hβ hη)
  have hcμ : c + μ ∈ S := S.add_mem hc hμS
  have m5 : γ + ε + c * η ∈ S := S.add_mem (S.add_mem hγS hε) (S.mul_mem hc hη)
  have m6 : γ + ε + (c + μ) * η ∈ S := S.add_mem (S.add_mem hγS hε) (S.mul_mem hcμ hη)
  have m7 : γ + c * ε + η ∈ S := S.add_mem (S.add_mem hγS (S.mul_mem hc hε)) hη
  have m8 : γ + (c + μ) * ε + η ∈ S := S.add_mem (S.add_mem hγS (S.mul_mem hcμ hε)) hη
  have x1 : 1 - α ∈ S := S.sub_mem S.one_mem hα
  have y1 : 1 - β ∈ S := S.sub_mem S.one_mem hβ
  have n5 : ∀ {R : K → Prop}, IdealLike S R → R ε → R η → ¬ R (γ + ε + c * η) := fun hR h1 h2 =>
    hR.not_one_add h1 h2 x1 (S.sub_mem hc hβ) (by linear_combination hγ)
  have n6 : ¬ P (γ + ε + (c + μ) * η) :=
    hP.not_one_add hPε hPη x1 (S.sub_mem hcμ hβ) (by linear_combination hγ)
  have n7 : ¬ P (γ + c * ε + η) :=
    hP.not_one_add hPε hPη (S.sub_mem hc hα) y1 (by linear_combination hγ)
  have n8 : ¬ P (γ + (c + μ) * ε + η) :=
    hP.not_one_add hPε hPη (S.sub_mem hcμ hα) y1 (by linear_combination hγ)
  by_cases hQη : Q η
  · by_cases hQε : Q ε
    · exact Or.inl (hunit _ m5 (n5 hP hPε hPη) (n5 hQ hQε hQη))
    · by_cases h7 : Q (γ + c * ε + η)
      · by_cases h8 : Q (γ + (c + μ) * ε + η)
        · exfalso
          apply hQε
          apply hQ.cancel hμ
          convert hQ.1 _ _ h8 h7 using 1
          ring
        · exact Or.inr (Or.inr (Or.inr (hunit _ m8 n8 h8)))
      · exact Or.inr (Or.inr (Or.inl (hunit _ m7 n7 h7)))
  · by_cases h5 : Q (γ + ε + c * η)
    · by_cases h6 : Q (γ + ε + (c + μ) * η)
      · exfalso
        apply hQη
        apply hQ.cancel hμ
        convert hQ.1 _ _ h6 h5 using 1
        ring
      · exact Or.inr (Or.inl (hunit _ m6 n6 h6))
    · exact Or.inl (hunit _ m5 (n5 hP hPε hPη) h5)

theorem plane_ring_core {S : Subring K} {P Q : K → Prop} (hP : IdealLike S P) (hQ : IdealLike S Q)
    (hunit : ∀ a ∈ S, ¬ P a → ¬ Q a → IsUnitIn S a)
    {ε η γ α β c μ : K} (hε : ε ∈ S) (hη : η ∈ S) (hα : α ∈ S) (hβ : β ∈ S) (hc : c ∈ S)
    (hμ : IsUnitIn S μ) (hγ : α * ε + β * η + γ = 1) :
    IsUnitIn S ε ∨ IsUnitIn S η ∨ IsUnitIn S (ε + μ * η) ∨
      (IsUnitIn S (γ + ε + c * η) ∨ IsUnitIn S (γ + ε + (c + μ) * η) ∨
        IsUnitIn S (γ + c * ε + η) ∨ IsUnitIn S (γ + (c + μ) * ε + η)) := by
  by_cases hUε : IsUnitIn S ε
  · exact Or.inl hUε
  by_cases hUη : IsUnitIn S η
  · exact Or.inr (Or.inl hUη)
  have hε' : P ε ∨ Q ε := by
    by_contra hh
    push Not at hh
    exact hUε (hunit ε hε hh.1 hh.2)
  have hη' : P η ∨ Q η := by
    by_contra hh
    push Not at hh
    exact hUη (hunit η hη hh.1 hh.2)
  by_cases hPP : P ε ∧ P η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hP hQ hunit hε hη hα hβ hc hμ hγ hPP.1 hPP.2)))
  by_cases hQQ : Q ε ∧ Q η
  · exact Or.inr (Or.inr (Or.inr (plane_ring_half hQ hP (fun a ha h1 h2 => hunit a ha h2 h1)
      hε hη hα hβ hc hμ hγ hQQ.1 hQQ.2)))
  refine Or.inr (Or.inr (Or.inl ?_))
  have m3 : ε + μ * η ∈ S := S.add_mem hε (S.mul_mem hμ.2.1 hη)
  rcases hε' with hPε | hQε
  · have hPη : ¬ P η := fun h => hPP ⟨hPε, h⟩
    have hQη : Q η := hη'.resolve_left hPη
    have hQε : ¬ Q ε := fun h => hQQ ⟨h, hQη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPη
      apply hP.cancel hμ
      convert hP.1 _ _ h3 hPε using 1
      ring
    · apply hQε
      convert hQ.1 _ _ h3 (hQ.2.1 μ hμ.2.1 η hQη) using 1
      ring
  · have hQη : ¬ Q η := fun h => hQQ ⟨hQε, h⟩
    have hPη : P η := hη'.resolve_right hQη
    have hPε : ¬ P ε := fun h => hPP ⟨h, hPη⟩
    refine hunit _ m3 (fun h3 => ?_) (fun h3 => ?_)
    · apply hPε
      convert hP.1 _ _ h3 (hP.2.1 μ hμ.2.1 η hPη) using 1
      ring
    · apply hQη
      apply hQ.cancel hμ
      convert hQ.1 _ _ h3 hQε using 1
      ring

theorem plane_partner {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    (hsym : ∀ x y, star (B x y) = B y x) {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N)
    (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S) (hdual : ∀ x, (∀ m ∈ N, B m x ∈ S) → x ∈ N) {v : V}
    (hv : v ∈ N) (hprim : ∀ c : K, c • v ∈ N → c ∈ S) {m0 : V} (hm0 : m0 ∈ N) (hne : B v m0 ≠ 0) :
    ∃ m ∈ N, B v m = 1 := by
  let A : AddSubgroup K :=
    { carrier := {a | ∃ m ∈ N, B v m = a}
      zero_mem' := ⟨0, N.zero_mem, by simp⟩
      add_mem' := by
        rintro _ _ ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
        exact ⟨m + m', N.add_mem hm hm', by simp⟩
      neg_mem' := by
        rintro _ ⟨m, hm, rfl⟩
        exact ⟨-m, N.neg_mem hm, by simp⟩ }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    rintro s hs _ ⟨m, hm, rfl⟩
    exact ⟨s • m, hsm s hs m hm, by simp⟩
  have hA0 : ∃ a ∈ A, a ≠ 0 := ⟨B v m0, ⟨m0, hm0, rfl⟩, hne⟩
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    rintro _ ⟨m, hm, rfl⟩
    simpa using hint v hv m hm
  obtain ⟨β, hβA, hβ0, hdiv⟩ := hS.principal A hA hA0 hAb
  obtain ⟨m1, hm1, hβ⟩ := hβA
  have hx : (star β)⁻¹ • v ∈ N := by
    apply hdual
    intro m hm
    have h1 := hdiv (B v m) ⟨m, hm, rfl⟩
    have e : B m ((star β)⁻¹ • v) = star (B v m * β⁻¹) := by
      rw [map_smul, smul_eq_mul, ← hsym v m, star_mul', star_inv₀]
      ring
    rw [e]
    exact hS.star_mem _ h1
  have hc := hprim _ hx
  have hβi : β⁻¹ ∈ S := by
    have := hS.star_mem _ hc
    rwa [star_inv₀, star_star] at this
  refine ⟨β⁻¹ • m1, hsm _ hβi _ hm1, ?_⟩
  rw [map_smul, smul_eq_mul, hβ, inv_mul_cancel₀ hβ0]

theorem plane_prim {S : Subring K} (hS : IsHermSemilocal S) (B : V →ₗ⋆[K] V →ₗ[K] K)
    {N : AddSubgroup V} (hsm : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) (hint : ∀ x ∈ N, ∀ y ∈ N, B x y ∈ S)
    {z w : V} (hz : z ∈ N) (hzw : B z w = 1) (hspan : ∃ t : K, t ≠ 0 ∧ t • w ∈ N) :
    ∃ α : K, α ≠ 0 ∧ α • w ∈ N ∧ ∀ c : K, c • (α • w) ∈ N → c ∈ S := by
  let A : AddSubgroup K :=
    { carrier := {c | c • w ∈ N}
      zero_mem' := by simp [N.zero_mem]
      add_mem' := by
        intro a b ha hb
        show (a + b) • w ∈ N
        rw [add_smul]
        exact N.add_mem ha hb
      neg_mem' := by
        intro a ha
        show (-a) • w ∈ N
        rw [neg_smul]
        exact N.neg_mem ha }
  have hA : ∀ s ∈ S, ∀ a ∈ A, s * a ∈ A := by
    intro s hs a ha
    show (s * a) • w ∈ N
    rw [mul_smul]
    exact hsm s hs _ ha
  obtain ⟨t, ht0, htw⟩ := hspan
  have hAb : ∃ t : K, t ≠ 0 ∧ ∀ a ∈ A, t * a ∈ S := by
    refine ⟨1, one_ne_zero, ?_⟩
    intro a ha
    have := hint z hz _ ha
    simpa [map_smul, hzw] using this
  obtain ⟨α, hαA, hα0, hdiv⟩ := hS.principal A hA ⟨t, htw, ht0⟩ hAb
  refine ⟨α, hα0, hαA, fun c hc => ?_⟩
  have h1 : c * α ∈ A := by
    show (c * α) • w ∈ N
    rwa [mul_smul]
  have := hdiv _ h1
  rwa [mul_assoc, mul_inv_cancel₀ hα0, mul_one] at this

def planeForm (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) : V →ₗ⋆[K] V →ₗ[K] K :=
  LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => h x y - b * h x z * h z y)
    (by intros; simp only [map_add (f := _), LinearMap.add_apply]; ring)
    (by intros; simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (by intros; simp only [map_add (f := _)]; ring)
    (by intros; simp only [map_smul, smul_eq_mul, RingHom.id_apply]; ring)

theorem planeForm_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (z : V) (b : K) (x y : V) :
    planeForm h z b x y = h x y - b * h x z * h z y := rfl

end Generic

section Ring

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def InI (p I : Ideal (𝓞 K)) (a : K) : Prop :=
  ∃ r s : 𝓞 K, s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p ∧ r ∈ I ∧
    a = algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s

theorem plane_idealLike {p : Ideal (𝓞 K)} (hp : p.IsPrime) (I : Ideal (𝓞 K))
    (hI : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) p, s ∉ I) : IdealLike (locRing p) (InI p I) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro _ _ ⟨r₁, s₁, hs₁, hr₁, rfl⟩ ⟨r₂, s₂, hs₂, hr₂, rfl⟩
    have h1 := algebraMap_ne_zero_of_mem_hcompl hp hs₁
    have h2 := algebraMap_ne_zero_of_mem_hcompl hp hs₂
    refine ⟨r₁ * s₂ - s₁ * r₂, s₁ * s₂, mul_mem hs₁ hs₂,
      I.sub_mem (I.mul_mem_right _ hr₁) (I.mul_mem_left _ hr₂), ?_⟩
    rw [div_sub_div _ _ h1 h2, map_sub, map_mul, map_mul, map_mul]
  · intro x hx a ha
    obtain ⟨r, s, hs, hr, rfl⟩ := ha
    obtain ⟨k, t, ht, rfl⟩ := (mem_locR_iff hp x).1 ((mem_locRing p x).1 hx)
    refine ⟨k * r, t * s, mul_mem ht hs, I.mul_mem_left k hr, ?_⟩
    rw [div_mul_div_comm, map_mul, map_mul]
  · rintro ⟨r, s, hs, hr, h1⟩
    have h0 := algebraMap_ne_zero_of_mem_hcompl hp hs
    rw [eq_div_iff h0, one_mul] at h1
    have hsr : s = r := RingOfIntegers.ext h1
    exact hI s hs (hsr ▸ hr)

theorem plane_unit {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K} (ha : a ∈ locRing p)
    (h1 : ¬ InI p p a) (h2 : ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) : IsUnitIn (locRing p) a := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).1 ((mem_locRing p a).1 ha)
  rw [isUnitIn_div_iff hp r hs, mem_hcompl_iff hp]
  exact ⟨fun hr => h1 ⟨r, s, hs, hr, rfl⟩, fun hr => h2 ⟨r, s, hs, hr, rfl⟩⟩

theorem plane_star₁ {p : Ideal (𝓞 K)} {a : K} (h : InI p p a) :
    InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (star a) := by
  obtain ⟨r, s, hs, hr, rfl⟩ := h
  refine ⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩
  · rw [mem_conjIdeal_iff, conjO_conjO]
    exact hr
  · rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

theorem plane_star₂ {p : Ideal (𝓞 K)} {a : K} (h : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a) :
    InI p p (star a) := by
  obtain ⟨r, s, hs, hr, rfl⟩ := h
  refine ⟨ReciprocityTheory.ChartRestriction.L3.conjO K r, ReciprocityTheory.ChartRestriction.L3.conjO K s, conjO_mem_hcompl hs, ?_, ?_⟩
  · exact (mem_conjIdeal_iff p r).1 hr
  · rw [algebraMap_conjO, algebraMap_conjO, star_div₀]

end Ring

theorem primitive_plane_local : Z0.PrimPlaneLoc := by
  intro K _ _ _ V _ _ _ h hK hs _ p hp N z b hN hz hprim hnu hb hbb hw
  obtain ⟨w, hzw, hww⟩ := hw
  have hS := isHermSemilocal_locRing hK hp
  have hpP := hp.isPrime
  have hsym : ∀ x y, star (h x y) = h y x := fun x y => hs.eq x y
  have hPl : IdealLike (locRing p) (InI p p) :=
    plane_idealLike hpP p (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').1)
  have hQl : IdealLike (locRing p) (InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p)) :=
    plane_idealLike hpP _ (fun s hs' => ((mem_hcompl_iff hpP s).1 hs').2)
  have hunit : ∀ a ∈ locRing p, ¬ InI p p a → ¬ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) a →
      IsUnitIn (locRing p) a := fun a ha h1 h2 => plane_unit hpP ha h1 h2

  have hζS : h z z ∈ locRing p := hN.int z hz z hz
  have hζr : star (h z z) = h z z := hsym z z
  have hJ : InI p p (h z z) ∧ InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
    by_cases h1 : InI p p (h z z)
    · refine ⟨h1, ?_⟩
      have := plane_star₁ h1
      rwa [hζr] at this
    · have h2 : InI p (Formalism.HermitianLatticesTheory.conjIdeal (K := K) p) (h z z) := by
        by_contra h2
        exact hnu (hunit _ hζS h1 h2)
      refine ⟨?_, h2⟩
      have := plane_star₂ h2
      rwa [hζr] at this
  have hu : IsUnitIn (locRing p) (1 - b * h z z) := by
    have hm : 1 - b * h z z ∈ locRing p := (locRing p).sub_mem (locRing p).one_mem ((locRing p).mul_mem hb hζS)
    refine hunit _ hm (fun h1 => hPl.2.2 ?_) (fun h1 => hQl.2.2 ?_)
    · convert hPl.add h1 (hPl.2.1 b hb _ hJ.1) using 1
      ring
    · convert hQl.add h1 (hQl.2.1 b hb _ hJ.2) using 1
      ring

  obtain ⟨q, hq⟩ : ∃ q : V →ₗ⋆[K] V →ₗ[K] K, ∀ x y, q x y = h x y - b * h x z * h z y :=
    ⟨planeForm h z b, planeForm_apply h z b⟩
  have hqsym : ∀ x y, star (q x y) = q y x := by
    intro x y
    rw [hq, hq, star_sub, star_mul', star_mul', hbb, hsym, hsym, hsym]
    ring
  have hqint : ∀ x ∈ N, ∀ y ∈ N, q x y ∈ locRing p := by
    intro x hx y hy
    rw [hq]
    exact (locRing p).sub_mem (hN.int x hx y hy)
      ((locRing p).mul_mem ((locRing p).mul_mem hb (hN.int x hx z hz)) (hN.int z hz y hy))
  have hqz : ∀ x, q z x = (1 - b * h z z) * h z x := by
    intro x
    rw [hq]
    ring
  have hqdual : ∀ x, (∀ m ∈ N, q m x ∈ locRing p) → x ∈ N := by
    intro x hx
    have hzx : h z x ∈ locRing p := by
      have := (locRing p).mul_mem hu.2.2 (hx z hz)
      rwa [hqz, ← mul_assoc, inv_mul_cancel₀ hu.1, one_mul] at this
    have hx' : x - (b * h z x) • z ∈ N := by
      apply hN.dual
      intro m hm
      convert hx m hm using 1
      rw [hq, map_sub, map_smul, smul_eq_mul]
      ring
    have := N.add_mem hx' (hN.smul_mem _ ((locRing p).mul_mem hb hzx) z hz)
    rwa [sub_add_cancel] at this

  have hwz : h w z = 1 := by rw [← hsym, hzw, star_one]
  have hqw : q w w = 0 := by rw [hq, hwz, hzw, hww]; ring
  obtain ⟨α, hα0, heN, heprim⟩ := plane_prim hS h hN.smul_mem hN.int hz hzw (hN.span w)
  have hze : h z (α • w) = α := by rw [map_smul, smul_eq_mul, hzw, mul_one]
  have hqee : q (α • w) (α • w) = 0 := by
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hqw, mul_zero]
  have hqez : q (α • w) z ≠ 0 := by
    rw [← hqsym, hqz, hze, star_mul']
    exact mul_ne_zero (star_ne_zero.mpr hu.1) (star_ne_zero.mpr hα0)
  generalize α • w = e at heN heprim hze hqee hqez

  obtain ⟨f₀, hf₀N, hef₀⟩ := plane_partner hS q hqsym hN.smul_mem hqint hqdual heN heprim hz hqez
  have hf₀e : q f₀ e = 1 := by rw [← hqsym, hef₀, star_one]
  obtain ⟨c₁, hc₁S, hc₁⟩ := exists_trace_eq hS (s := -q f₀ f₀)
    ((locRing p).neg_mem (hqint f₀ hf₀N f₀ hf₀N)) (by rw [star_neg, hqsym])
  have hfN : f₀ + c₁ • e ∈ N := N.add_mem hf₀N (hN.smul_mem c₁ hc₁S e heN)
  have hqef : q e (f₀ + c₁ • e) = 1 := by
    rw [map_add (f := _), map_smul, smul_eq_mul, hqee, mul_zero, add_zero, hef₀]
  have hqff : q (f₀ + c₁ • e) (f₀ + c₁ • e) = 0 := by
    simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, hqee, hef₀, hf₀e]
    linear_combination hc₁
  generalize f₀ + c₁ • e = f at hfN hqef hqff
  have hqfe : q f e = 1 := by rw [← hqsym, hqef, star_one]

  obtain ⟨t, htN, hzt⟩ := plane_partner hS h hsym hN.smul_mem hN.int hN.dual hz hprim heN
    (by rw [hze]; exact hα0)

  have hgN : t - q f t • e - q e t • f ∈ N :=
    N.sub_mem (N.sub_mem htN (hN.smul_mem _ (hqint f hfN t htN) e heN))
      (hN.smul_mem _ (hqint e heN t htN) f hfN)
  have hqeg : q e (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqee, hqef]
    ring
  have hqfg : q f (t - q f t • e - q e t • f) = 0 := by
    simp only [map_sub, map_smul, smul_eq_mul, hqff, hqfe]
    ring
  have hzg : q f t * h z e + q e t * h z f + h z (t - q f t • e - q e t • f) = 1 := by
    simp only [map_sub, map_smul, smul_eq_mul, hzt]
    ring
  have hαS := hqint f hfN t htN
  have hβS := hqint e heN t htN
  generalize q f t = α' at hgN hqeg hqfg hzg hαS
  generalize q e t = β' at hgN hqeg hqfg hzg hβS
  generalize t - α' • e - β' • f = g at hgN hqeg hqfg hzg
  have hqge : q g e = 0 := by rw [← hqsym, hqeg, star_zero]
  have hqgf : q g f = 0 := by rw [← hqsym, hqfg, star_zero]
  obtain ⟨c, hcS, hc⟩ := exists_trace_eq hS (s := -q g g)
    ((locRing p).neg_mem (hqint g hgN g hgN)) (by rw [star_neg, hqsym])
  obtain ⟨θ, -, hμ⟩ := hS.unram
  have hμs : star (θ - star θ) = -(θ - star θ) := by rw [star_sub, star_star]; ring
  generalize θ - star θ = μ at hμ hμs

  have key : ∀ s a d : K, s ∈ locRing p → a ∈ locRing p → d ∈ locRing p →
      star s * s * q g g + star a * d + star d * a = 0 →
      IsUnitIn (locRing p) (s * h z g + a * h z e + d * h z f) → ∃ y ∈ N, h z y = 1 ∧ h y y = b := by
    intro s a d hs' ha hd hn hU
    have hXN : s • g + a • e + d • f ∈ N :=
      N.add_mem (N.add_mem (hN.smul_mem s hs' g hgN) (hN.smul_mem a ha e heN)) (hN.smul_mem d hd f hfN)
    have hzX : h z (s • g + a • e + d • f) = s * h z g + a * h z e + d * h z f := by
      simp only [map_add (f := _), map_smul, smul_eq_mul]
    have hqX : q (s • g + a • e + d • f) (s • g + a • e + d • f) = 0 := by
      rw [← hn]
      simp only [map_add (f := _), map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        starRingEnd_apply, RingHom.id_apply, hqee, hqff, hqef, hqfe, hqeg, hqge, hqfg, hqgf]
      ring
    refine ⟨(s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f),
      hN.smul_mem _ hU.2.2 _ hXN, ?_, ?_⟩
    · rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
    · have h1 : h z ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 1 := by
        rw [map_smul, smul_eq_mul, hzX, inv_mul_cancel₀ hU.1]
      have h2 : h ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) z = 1 := by
        rw [← hsym, h1, star_one]
      have h3 := hq ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
        ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
      rw [h1, h2] at h3
      have h4 : q ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f))
          ((s * h z g + a * h z e + d * h z f)⁻¹ • (s • g + a • e + d • f)) = 0 := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hqX, mul_zero]
      rw [h4] at h3
      linear_combination -h3
  have hS0 : (0 : K) ∈ locRing p := (locRing p).zero_mem
  have hS1 : (1 : K) ∈ locRing p := (locRing p).one_mem
  have hμS : μ ∈ locRing p := hμ.2.1
  have hcμ : c + μ ∈ locRing p := (locRing p).add_mem hcS hμS
  rcases plane_ring_core hPl hQl hunit (hN.int z hz e heN) (hN.int z hz f hfN) hαS hβS hcS hμ hzg with
    h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact key 0 1 0 hS0 hS1 hS0 (by simp) (by convert h1 using 1; ring)
  · exact key 0 0 1 hS0 hS0 hS1 (by simp) (by convert h1 using 1; ring)
  · exact key 0 1 μ hS0 hS1 hμS (by rw [hμs]; simp) (by convert h1 using 1; ring)
  · exact key 1 1 c hS1 hS1 hcS (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 1 (c + μ) hS1 hS1 hcμ (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)
  · exact key 1 c 1 hS1 hcS hS1 (by rw [star_one]; linear_combination hc) (by convert h1 using 1; ring)
  · exact key 1 (c + μ) 1 hS1 hcμ hS1 (by rw [star_one, star_add, hμs]; linear_combination hc)
      (by convert h1 using 1; ring)

end Formalism.L2.SG.Pf.LatDictZ.Z2
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlue
noncomputable section

open NumberField Matrix IsDedekindDomain
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.LatDictZ.Z5

open Formalism.MainNotions.S PIW.AdelClassFin Formalism.L2.SG.Pf.LatDictZ

theorem adelic_gluing : Z0.AdelGlue := by
  intro I r s z M hMfg hMsp hfin γ hγU hγs hγz hloc
  classical

  let Q : Set (HeightOneSpectrum (𝓞 I.F)) := {q | ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧
    locE I p M ≠ locE I p I.L ∧ p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal}
  have hQ : Q.Finite := by
    have := DictRing.nonempty_places (F := I.F)
    refine (hfin.image fun p => if hp : p.IsMaximal then under I p hp else Classical.arbitrary _).subset ?_
    rintro q ⟨p, hp, hne, hq⟩
    refine ⟨p, ⟨hp, hne⟩, ?_⟩
    simp only [dif_pos hp]
    exact HeightOneSpectrum.ext hq
  have hQex : ∀ q ∈ Q, ∃ p : Ideal (𝓞 I.E), p.IsMaximal ∧
      p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal :=
    fun q ⟨p, hp, _, hq⟩ => ⟨p, hp, hq⟩

  let g : HeightOneSpectrum (𝓞 I.F) → GL (Fin I.n) I.E := fun q =>
    if h : q ∈ Q then γ (Classical.choose (hQex q h)) else 1
  have hgU : ∀ q, g q ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := fun q => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγU _
    · simp only [g, dif_neg h]; exact one_mem _
  have hgs : ∀ q a, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ s a = s a := fun q a => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγs _ a
    · simp only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]
  have hgz : ∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z = z := fun q => by
    by_cases h : q ∈ Q
    · simp only [g, dif_pos h]; exact hγz _
    · simp only [g, dif_neg h, Units.val_one, Matrix.one_mulVec]
  have hgloc : ∀ q ∈ Q, ∀ p : Ideal (𝓞 I.E), p.IsMaximal →
      p.comap (algebraMap (𝓞 I.F) (𝓞 I.E)) = q.asIdeal →
      ∀ v, v ∈ locE I p M ↔ ∃ w ∈ locE I p I.L, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ w = v := by
    intro q hq p hp hpq v
    have hc := Classical.choose_spec (hQex q hq)
    simp only [g, dif_pos hq]
    rw [loc_congr I hp hc.1 (hpq.trans hc.2.symm) M, loc_congr I hp hc.1 (hpq.trans hc.2.symm) I.L]
    exact hloc _ hc.1 v

  let Qs := hQ.toFinset
  let ε : HeightOneSpectrum (𝓞 I.F) → I.E ⊗[I.F] Af I.F := fun q => iA I (eT {q})
  let φ : I.E ⊗[I.F] Af I.F := iA I (eT Qᶜ)
  have horth : Orth Qs ε := fun i _ j _ => by
    simp only [ε]
    rw [← map_mul, eT_orth]
    split_ifs <;> simp
  have hφε : ∀ i ∈ Qs, φ * ε i = 0 := fun i hi => by
    simp only [φ, ε]
    rw [← map_mul, eT_compl_mul (hQ.mem_toFinset.1 hi), map_zero]
  have hsum : φ + ∑ i ∈ Qs, ε i = 1 := by
    simp only [φ, ε]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← map_add (f := _), eT_sum hQ, map_one]

  let G : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun q =>
    (g q : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))
  let Gi : HeightOneSpectrum (𝓞 I.F) → Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) := fun q =>
    (((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))
  have hGGi : ∀ q, G q * Gi q = 1 := fun q => by
    simp only [G, Gi]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGiG : ∀ q, Gi q * G q = 1 := fun q => by
    simp only [G, Gi]
    rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXY : gl Qs ε 1 G * gl Qs ε 1 Gi = 1 := by
    rw [gl_mul horth]; simp only [hGGi, mul_one]; exact gl_const _ _ _
  have hYX : gl Qs ε 1 Gi * gl Qs ε 1 G = 1 := by
    rw [gl_mul horth]; simp only [hGiG, mul_one]; exact gl_const _ _ _

  let σR := Formalism.UG.sigR I.cm.sig (Af I.F)
  let J' := I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
  have hσε : ∀ i ∈ Qs, σR (ε i) = ε i := fun i _ => by
    simp only [σR, ε]
    rw [Algebra.TensorProduct.includeRight_apply]
    exact DictLat.sigR_one_tmul I _
  have hcG : ∀ q, Formalism.UG.cT σR (G q) =
      (Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E)).map
        (Formalism.UG.inclE (F := I.F) (Af I.F)) := fun q => by
    ext a b
    simp only [Formalism.UG.cT, G, σR, Matrix.map_apply, Matrix.transpose_apply, DictLat.sigR_inclE, starRingEnd_apply]
  have hGu : ∀ q, Formalism.UG.cT σR (G q) * J' * G q = J' := fun q => by
    rw [hcG]
    simp only [G, J']
    rw [← Matrix.map_mul, ← Matrix.map_mul]
    exact congrArg (fun N => N.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
      (show Formalism.UG.cT (starRingEnd I.E) (g q : Matrix (Fin I.n) (Fin I.n) I.E) * I.J *
        (g q : Matrix (Fin I.n) (Fin I.n) I.E) = I.J from hgU q)
  have hXU : Formalism.UG.cT σR (gl Qs ε 1 G) * J' * gl Qs ε 1 G = J' := by
    rw [cT_gl σR hσε, Formalism.UG.cT_one]
    conv_lhs => rw [show J' = gl Qs ε J' (fun _ => J') from (gl_const _ _ _).symm]
    rw [gl_mul horth, gl_mul horth]
    simp only [hGu, mul_one, one_mul]
    exact gl_const _ _ _
  let xg : GL (Fin I.n) (I.E ⊗[I.F] Af I.F) := ⟨gl Qs ε 1 G, gl Qs ε 1 Gi, hXY, hYX⟩
  have hxU : xg ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := hXU
  let x : I.Gf := ⟨xg, hxU⟩
  have hfx : I.fmat x = gl Qs ε 1 G := rfl
  have hfxi : I.fmat x⁻¹ = gl Qs ε 1 Gi := rfl

  have hfix : ∀ u : Fin I.n → I.E, (∀ q, (g q : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ u = u) →
      I.fmat x *ᵥ iv I u = iv I u := by
    intro u hu
    rw [hfx, gl_mulVec, Matrix.one_mulVec, Finset.sum_eq_zero (fun q _ => ?_), add_zero]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [G]
    rw [dictTop_map_mulVec, hu, sub_self, smul_zero]
  refine ⟨x, fun a => hfix _ (fun q => hgs q a), hfix _ hgz, ?_⟩

  ext v
  show I.fmat x⁻¹ *ᵥ iv I v ∈ I.Lf ↔ v ∈ M
  rw [hfxi]
  have hdec : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, y ∈ I.Lf ↔ φ • y ∈ I.Lf ∧ ∀ q ∈ Qs, ε q • y ∈ I.Lf := by
    intro y
    refine ⟨fun h => ⟨DictLat.Lf_smul I (iA_mem I (eT_mem _)) h,
      fun q _ => DictLat.Lf_smul I (iA_mem I (eT_mem _)) h⟩, fun ⟨h0, h1⟩ => ?_⟩
    have hy : y = φ • y + ∑ q ∈ Qs, ε q • y := by
      rw [← Finset.sum_smul, ← add_smul, hsum, one_smul]
    rw [hy]
    exact add_mem h0 (Submodule.sum_mem _ h1)
  have hproj : ∀ q ∈ Qs, ε q • (gl Qs ε 1 Gi *ᵥ iv I v) =
      ε q • iv I ((((g q)⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v) := fun q hq => by
    rw [gl_proj horth _ _ _ hq]
    simp only [Gi]
    rw [dictTop_map_mulVec]
  have hproj0 : φ • (gl Qs ε 1 Gi *ᵥ iv I v) = φ • iv I v := by
    rw [gl_proj0 hφε, Matrix.one_mulVec]
  rw [hdec, hproj0]
  constructor
  · rintro ⟨h0, h1⟩
    refine Formalism.HermitianLatticesTheory.locBasic_lg (fun p => Formalism.HermitianLatticesTheory.hcompl (K := I.E) p)
      (fun p hp s hs => by have := hp.isPrime; exact Formalism.HermitianLatticesTheory.locBasic_hcompl_not_mem (K := I.E) p s hs)
      M v (fun p hp => ?_)
    show v ∈ locE I p M
    by_cases hq : under I p hp ∈ Q
    · have h2 := h1 _ (hQ.mem_toFinset.2 hq)
      rw [hproj _ (hQ.mem_toFinset.2 hq)] at h2
      obtain ⟨a, ha, haw⟩ := descent I (under I p hp) (eT_mem _) (eT_of_mem (Set.mem_singleton _)) _ h2
      rw [hgloc _ hq p hp rfl]
      exact ⟨_, (loc_iff I p hp _ _).2 ⟨a, ha, haw⟩,
        by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
    · obtain ⟨a, ha, haw⟩ := descent I (under I p hp) (eT_mem _) (eT_of_mem hq) _ h0
      have hne : locE I p M = locE I p I.L := by
        by_contra hne
        exact hq ⟨p, hp, hne, rfl⟩
      rw [hne]
      exact (loc_iff I p hp _ _).2 ⟨a, ha, haw⟩
  · intro hv
    refine ⟨?_, fun q hq => ?_⟩
    · apply glue I Qᶜ v
      intro q hq
      have hker : RingHom.ker (algebraMap (𝓞 I.F) (𝓞 I.E)) ≤ q.asIdeal := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 (alg_inj I)]
        exact bot_le
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 I.E) q.asIdeal hker
      have hne : locE I p M = locE I p I.L := by
        by_contra hne
        exact hq ⟨p, hp, hne, hpq⟩
      have h3 : v ∈ locE I p M := Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv
      rw [hne] at h3
      obtain ⟨a, ha, haw⟩ := (loc_iff I p hp _ _).1 h3
      exact ⟨a, hpq ▸ ha, haw⟩
    · rw [hproj q hq]
      apply glue I {q} _
      intro q' hq'
      rw [Set.mem_singleton_iff] at hq'
      subst hq'
      have hqQ := hQ.mem_toFinset.1 hq
      obtain ⟨p, hp, hpq⟩ := hQex q' hqQ
      obtain ⟨w, hw, hgw⟩ := (hgloc q' hqQ p hp hpq v).1 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ M hv)
      have hw' : w = (((g q')⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ v := by
        rw [← hgw, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      obtain ⟨a, ha, haw⟩ := (loc_iff I p hp _ _).1 hw
      exact ⟨a, hpq ▸ ha, hw' ▸ haw⟩

end Formalism.L2.SG.Pf.LatDictZ.Z5
end
end

namespace Formalism.L2.SG.Pf.LatDictZ

theorem anisotropic_vector_orbit : LatDictZ.ZOrbit :=
  zOrbit_of_open Z2.primitive_plane_local Z5.adelic_gluing

end Formalism.L2.SG.Pf.LatDictZ
end

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions

theorem latRowLat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatRowLat X u :=
  latRowLat_of LatDictZ.lattice_genus X u

theorem latSurj {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : LatSurj X u :=
  latSurj_of LatDictZ.anisotropic_vector_orbit X u

theorem lattice_steps_hold : LatticeRowBijectionClassFinite := fun _ X hK u =>
  ⟨latRowLat X u, latSurj X u, latInj X u, Formalism.L2.SG.Closed.ClassFin_holds X u hK⟩

end Formalism.L2.SG.Pf
