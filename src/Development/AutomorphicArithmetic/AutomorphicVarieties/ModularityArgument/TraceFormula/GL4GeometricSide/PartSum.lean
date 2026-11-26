module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DiracW
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LefData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBound

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HarmDom
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem mem_lo {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, c ≤ b → c ∈ S) (c : Fin n) :
    c ∈ S ↔ (c : ℕ) < S.card := by
  constructor
  · intro hc
    have hsub : Finset.Iic c ⊆ S := fun b hb => hS c hc b (Finset.mem_Iic.1 hb)
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h
    omega
  · intro hlt
    by_contra hc
    have hsub : S ⊆ Finset.Iio c := fun b hb => Finset.mem_Iio.2 (by
      by_contra h
      exact hc (hS b hb c (not_lt.1 h)))
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h
    omega

private theorem mem_hi {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, b ≤ c → c ∈ S) (c : Fin n) :
    c ∈ S ↔ n ≤ (c : ℕ) + S.card := by
  constructor
  · intro hc
    have hsub : Finset.Ici c ⊆ S := fun b hb => hS c hc b (Finset.mem_Ici.mp hb)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hle
    by_contra hc
    have hsub : S ⊆ Finset.Ioi c := by
      intro b hb
      rw [Finset.mem_Ioi]
      by_contra hbc
      exact hc (hS b hb c (not_lt.mp hbc))
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    have := c.isLt
    omega

private theorem harmonic_dominant_weight {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (L : Fin n → ℕ) (hL : IsLev lam L) :
    Dom (muQ lam L) ∧ domC (muQ lam L - rhoV n) + rhoV n = twoL lam := by
  obtain ⟨hmono, hlev⟩ := hL
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℕ, ∀ a, D a = #{b | L b < L a} := ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℕ, ∀ a, U a = #{b | L a < L b} := ⟨_, fun _ => rfl⟩
  have hDlo : ∀ a c, L c < L a ↔ (c : ℕ) < D a := by
    intro a c
    have h := mem_lo (Finset.filter (fun b => L b < L a) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_le_of_lt (hmono hcb) hb) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hD]
    exact h
  have hUhi : ∀ a c, L a < L c ↔ n ≤ (c : ℕ) + U a := by
    intro a c
    have h := mem_hi (Finset.filter (fun b => L a < L b) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_lt_of_le hb (hmono hcb)) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hU]
    exact h
  have hDa : ∀ a : Fin n, D a ≤ a := fun a => not_lt.mp (fun h => lt_irrefl _ ((hDlo a a).mpr h))
  have hUa : ∀ a : Fin n, (a : ℕ) + U a < n := fun a => not_le.mp (fun h => lt_irrefl _ ((hUhi a a).mpr h))
  let f : Fin n → Fin n := fun a => ⟨D a + (n - 1 - U a) - a, by
    have := hDa a
    have := hUa a
    omega⟩
  have hfv : ∀ a, ((f a : Fin n) : ℕ) = D a + (n - 1 - U a) - a := fun a => rfl
  have hLf : ∀ a, L (f a) = L a := by
    intro a
    rcases lt_trichotomy (L (f a)) (L a) with h | h | h
    · have h1 := (hDlo a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
    · exact h
    · have h1 := (hUhi a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
  have hDf : ∀ a, D (f a) = D a := by
    intro a
    rw [hD, hD, hLf]
  have hUf : ∀ a, U (f a) = U a := by
    intro a
    rw [hU, hU, hLf]
  have hinv : Function.Involutive f := by
    intro a
    apply Fin.ext
    rw [hfv (f a), hDf, hUf, hfv]
    have := hDa a
    have := hUa a
    omega
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hLab := hmono hab.le
    have hlab := hl hab.le
    have hUab : U b ≤ U a := by
      rw [hU, hU]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_le_of_lt hLab hc
    have hDab : D a ≤ D b := by
      rw [hD, hD]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_lt_of_le hc hLab
    have e1 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have e2 : (((lam a - lam b).toNat : ℕ) : ℝ) = (lam a : ℝ) - lam b := by
      have h := congrArg (Int.cast : ℤ → ℝ) e1
      push_cast at h
      exact h
    refine ⟨2 * (lam a - lam b).toNat + (U a - U b) + (D b - D a), ?_⟩
    simp only [muQ, rhoU]
    rw [← hU a, ← hU b, ← hD a, ← hD b]
    push_cast [Nat.cast_sub hUab, Nat.cast_sub hDab, e2]
    ring
  · obtain ⟨y, hy⟩ : ∃ y : Wt n, ∀ a, y a = 2 * (lam a : ℝ) + rhoV n a := ⟨_, fun _ => rfl⟩
    have hyA : Antitone y := by
      intro a b hab
      rw [hy, hy]
      have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
      have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      simp only [rhoV]
      linarith
    have hx : ∀ a, (muQ lam L - rhoV n) (f a) = y a := by
      intro a
      have hnat : ((f a : ℕ)) + a + 1 + U a = D a + n := by
        rw [hfv]
        have := hDa a
        have := hUa a
        omega
      have hreal : (((f a : ℕ)) : ℝ) + ((a : ℕ) : ℝ) + 1 + (U a : ℝ) = (D a : ℝ) + n := by
        exact_mod_cast hnat
      simp only [Pi.sub_apply, muQ, rhoU, rhoV]
      rw [← hU (f a), ← hD (f a), hUf, hDf, hlev _ _ (hLf a), hy]
      simp only [rhoV]
      linarith
    let w : Equiv.Perm (Fin n) := Function.Involutive.toPerm f hinv
    have hxy : muQ lam L - rhoV n = y ∘ w := by
      funext a
      have h := hx (f a)
      rw [hinv a] at h
      exact h
    have R := (rearr n).2.1 y
    rw [hxy, R.2.2.2.1 w, R.2.2.1 hyA]
    funext a
    simp only [Pi.add_apply, twoL, hy]
    ring

theorem UpperTheory.RealTr.harmDom :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ μ ∈ harmSet lam, Dom μ ∧ domC (μ - rhoV n) + rhoV n = twoL lam := by
  intro n lam hl μ hμ
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  obtain ⟨lev, hlev, rfl⟩ := hμ
  exact harmonic_dominant_weight lam hl _ hlev
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HomSurj
noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem kspan_stb {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) :
    Stb F (Formalism.REAL.kSpan (fun _ => true) F x) := by
  intro a b y hy
  rw [Formalism.REAL.kSpan, Submodule.mem_sInf] at hy ⊢
  intro S hS
  exact hS.2 a b rfl y (hy S hS)

private theorem proj_comm {n : ℕ} {N : Type} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    {F : Fin n → Fin n → Module.End ℂ N} (hF : UF F) (S : Submodule ℂ N) [S.HasOrthogonalProjection]
    (hS : Stb F S) (a b : Fin n) (y : N) :
    S.starProjection (F a b y) = F a b (S.starProjection y) := by
  have hz : F a b (y - S.starProjection y) ∈ Sᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [← hF.unit b a w]
    exact Submodule.inner_right_of_mem_orthogonal (hS b a w hw)
      (Submodule.sub_starProjection_mem_orthogonal y)
  refine Submodule.eq_starProjection_of_mem_orthogonal' (hS a b _ (S.starProjection_apply_mem y)) hz ?_
  rw [← map_add (f := _), add_sub_cancel]

theorem UpperTheory.RealTr.homSurj :
    ∀ (n : ℕ) (N V : Type) [NormedAddCommGroup N] [InnerProductSpace ℂ N] [FiniteDimensional ℂ N] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (F : Fin n → Fin n → Module.End ℂ N) (K : Fin n → Fin n → Module.End ℂ V), UF F → UF K → LocF K → ∀ (ν : Wt n) (φ : hw F ν →ₗ[ℂ] hw K ν), ∃ t ∈ homL F K, (∀ x : hw F ν, t x = φ x) ∧ ∀ μ, μ ≠ ν → ∀ x ∈ hw F μ, t x = 0 := by
  intro n N V _ _ _ _ _ F K hF hK hL ν φ
  have hKR : Formalism.REAL.KRel (fun _ => true) F := Formalism.REAL.glRel_kRel _ F hF.gl
  have hKU : Formalism.REAL.KUnit (fun _ => true) F := fun a b _ => hF.unit a b
  obtain ⟨m, x, μ, hx, horth, hsup⟩ := Formalism.REAL.kDecomp N n (fun _ => true) F ⊤ inferInstance hKR hKU
    (fun a b _ y _ => trivial)
  obtain ⟨P, hP⟩ : ∃ P : Fin m → N →L[ℂ] N,
      ∀ i, P i = (Formalism.REAL.kSpan (fun _ => true) F (x i)).starProjection := ⟨_, fun _ => rfl⟩
  have hPmem : ∀ i y, P i y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) := by
    intro i y
    rw [hP]
    exact Submodule.starProjection_apply_mem _ y
  have hPself : ∀ i y, y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → P i y = y := by
    intro i y hy
    rw [hP]
    exact Submodule.starProjection_eq_self_iff.mpr hy
  have hPorth : ∀ i j y, j ≠ i → y ∈ Formalism.REAL.kSpan (fun _ => true) F (x j) → P i y = 0 := by
    intro i j y hji hy
    rw [hP]
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (zero_mem _) (fun w hw => ?_)
    rw [sub_zero]
    exact horth j i hji y hy w hw
  have hcomm : ∀ i a b y, P i (F a b y) = F a b (P i y) := by
    intro i a b y
    rw [hP]
    exact proj_comm hF _ (kspan_stb F (x i)) a b y
  have hcomp : ∀ (μ' : Wt n) (y : N), KHighest (fun _ => true) F μ' y →
      ∀ i, KHighest (fun _ => true) F μ' (P i y) := by
    intro μ' y hy i
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hcomm, hy.1 a, map_smul]
    · rw [← hcomm, hy.2 a b hab he, map_zero]
  have huniq : ∀ (μ' : Wt n) (y : N) i, KHighest (fun _ => true) F μ' y →
      y ∈ Formalism.REAL.kSpan (fun _ => true) F (x i) → y = 0 ∨ μ' = μ i ∧ ∃ c : ℂ, y = c • x i :=
    fun μ' y i hy hm => Formalism.REAL.kHiUniq N n _ F (μ i) μ' (x i) y hKR hKU (hx i).2.2 hm hy
  have hsum : ∀ y : N, y = ∑ i, P i y := by
    intro y
    have hy : y ∈ ⨆ i, Formalism.REAL.kSpan (fun _ => true) F (x i) := by
      rw [hsup]
      trivial
    refine Submodule.iSup_induction (motive := fun y => y = ∑ i, P i y) _ hy ?_ ?_ ?_
    · intro j z hz
      rw [Finset.sum_eq_single j (fun i _ hij => hPorth i j z (Ne.symm hij) hz)
        (fun h => absurd (Finset.mem_univ j) h), hPself j z hz]
    · simp
    · intro a b ha hb
      simp only [map_add (f := _), Finset.sum_add_distrib]
      rw [← ha, ← hb]
  have hg : ∀ i, ∃ g : N →ₗ[ℂ] V, (∀ a b (y : N), g (F a b y) = K a b (g y)) ∧
      (μ i = ν → ∀ h : x i ∈ hw F ν, g (x i) = (φ ⟨x i, h⟩ : V)) ∧ (μ i ≠ ν → g = 0) := by
    intro i
    by_cases h : μ i = ν
    · have hxi : x i ∈ hw F ν := by
        rw [← h]
        exact (hx i).2.2
      obtain ⟨S, hSf, hvS, hSstb⟩ := hL (φ ⟨x i, hxi⟩ : V)
      obtain ⟨g, hg1, hg2⟩ := GlobalTheory.CompanionTheory.TransS.InfChar.hHWMap n (fun _ => true) N V F K ν (x i)
        (φ ⟨x i, hxi⟩ : V) S (fun a b c d _ _ => hF.gl a b c d) (fun a b _ => hF.unit a b)
        (fun a b c d _ _ => hK.gl a b c d) (fun a b _ => hK.unit a b) (hx i).2.1 hxi
        (φ ⟨x i, hxi⟩).2 hSf (fun a b _ => hSstb a b) hvS
      exact ⟨g, fun a b y => hg2 a b rfl y, fun _ _ => hg1, fun hne => absurd h hne⟩
    · exact ⟨0, fun a b y => by simp, fun h' => absurd h' h, fun _ => rfl⟩
  choose g hgL hgv hg0 using hg
  have happ : ∀ y, (∑ i, (g i).comp (P i : N →ₗ[ℂ] N)) y = ∑ i, g i (P i y) := by
    intro y
    simp [LinearMap.sum_apply]
  refine ⟨∑ i, (g i).comp (P i : N →ₗ[ℂ] N), ?_, ?_, ?_⟩
  · refine Submodule.sum_mem _ (fun i _ => ?_)
    show ∀ a b (y : N), (g i).comp (P i : N →ₗ[ℂ] N) (F a b y) = K a b ((g i).comp (P i : N →ₗ[ℂ] N) y)
    intro a b y
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
    rw [hcomm i a b y]
    exact hgL i a b _
  · intro y
    have key : ∀ i, g i (P i y) = (φ ⟨P i y, hcomp ν y y.2 i⟩ : V) := by
      intro i
      rcases huniq ν (P i y) i (hcomp ν y y.2 i) (hPmem i y) with h0 | ⟨hμ, c, hc⟩
      · have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = 0 := Subtype.ext h0
        rw [e, map_zero, Submodule.coe_zero, h0, map_zero]
      · have hxi : x i ∈ hw F ν := by
          rw [hμ]
          exact (hx i).2.2
        have e : (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν) = c • ⟨x i, hxi⟩ := Subtype.ext hc
        rw [e, map_smul, Submodule.coe_smul, hc, map_smul, hgv i hμ.symm hxi]
    have hs : (∑ i, (⟨P i y, hcomp ν y y.2 i⟩ : hw F ν)) = y := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      exact (hsum y).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [happ, Finset.sum_congr rfl (fun i _ => key i), ← Submodule.coe_sum, ← map_sum, hs]
  · intro μ' hne y hy
    rw [happ]
    refine Finset.sum_eq_zero (fun i _ => ?_)
    by_cases h : μ i = ν
    · rcases huniq μ' (P i y) i (hcomp μ' y hy i) (hPmem i y) with h0 | ⟨hμ, _⟩
      · rw [h0, map_zero]
      · exact absurd (hμ.trans h) hne
    · rw [hg0 i h, LinearMap.zero_apply]
end
end

open UpperTheory.V.Z.GSp4Splitting PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD PositivityTheory.Rg.BcB.Desc

noncomputable section

namespace UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open Finset UpperTheory.RealTr GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

variable {n : ℕ}

private theorem part_sum (c : Fin n → Fin n → ℕ) (Q : Fin n → ℝ)
    (hQ : ∀ x, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)))
    (S : Finset (Fin n)) :
    ∑ x ∈ S, Q x = ∑ a, ∑ b, (c a b : ℝ) * ((if a ∈ S then 1 else 0) - (if b ∈ S then 1 else 0)) := by
  simp only [hQ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']

private theorem domLE_of {ν m : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m - ν)) : DomLE ν m := by
  obtain ⟨c, hc, hQ⟩ := h
  refine ⟨fun k => ?_, ?_⟩
  · rw [← sub_nonneg, ← Finset.sum_sub_distrib]
    have hs := part_sum c (m - ν) hQ (univ.filter fun a : Fin n => (a : ℕ) < k)
    simp only [Pi.sub_apply] at hs
    rw [hs]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h0 : c a b = 0
    · simp [h0]
    have hab : (a : ℕ) < b := hc a b h0
    refine mul_nonneg (Nat.cast_nonneg _) ?_
    simp only [mem_filter, mem_univ, true_and]
    split_ifs with h1 h2 h2
    · simp
    · simp
    · omega
    · simp
  · have hs := part_sum c (m - ν) hQ univ
    simp only [Pi.sub_apply, mem_univ, if_true, sub_self, mul_zero, Finset.sum_const_zero,
      Finset.sum_sub_distrib] at hs
    linarith

private theorem int_of (lam : Fin n → ℤ) {ν : Fin n → ℝ} (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) :
    ∃ z : Fin n → ℤ, ν = wtR z := by
  obtain ⟨c, -, hQ⟩ := h
  refine ⟨fun x => m0Z lam x - ∑ a, ∑ b, (c a b : ℤ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0)), ?_⟩
  funext x
  have hx := hQ x
  simp only [Pi.sub_apply, m0] at hx
  simp only [wtR, m0Z]
  push_cast
  linarith

private theorem harm_of (lam : Fin n → ℤ) (hl : Antitone lam) {ν : Fin n → ℝ} (hν : Antitone ν)
    (h : inCone (fun a => (a : ℕ)) (m0 lam - ν)) (hd : LSq lam ≤ spinSq ν) : ν ∈ harmSet lam := by
  have hle := domLE_of h
  obtain ⟨z, rfl⟩ := int_of lam h
  have hz : Antitone z := fun a b hab => by
    have := hν hab
    simpa [wtR] using this
  rw [harmSet_eq]
  refine Finset.mem_image_of_mem _ (GlobalTheory.T.harmonic_of_norm_bound lam hl z hz hle
    (Tuple.sort fun a => -(wtR z - rhoV n) a) (((rearr n).2.1 (wtR z - rhoV n)).1) ?_)
  refine le_of_eq_of_le ?_ hd
  unfold LSq nsq m0 rhoV
  exact Finset.sum_congr rfl fun a _ => by ring

end UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism

open UpperTheory.RealTr UpperTheory.V.Z.GSp4Splitting.LowRankIsomorphism in
theorem UpperTheory.V.Z.GSp4Splitting.lowIso2 :
    LowIso := by
  intro n lam hl E T hT V _ _ E1 E2 σ A hc ⟨ν, hne, hcone⟩
  have hK : UF (kF E1 E2) := ⟨GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair, hc.pair.unitK⟩
  have hL : LocF (kF E1 E2) := fun x => by
    obtain ⟨S, h1, h2, -, h3, -⟩ := hc.der.2 x
    exact ⟨S, h1, h2, h3⟩
  have hneK : hw (kF E1 E2) ν ≠ ⊥ := hne
  obtain ⟨-, -, hρ, -, hdom, -⟩ := rearr n
  have hD : Dom ν := (irrCh n V (kF E1 E2) hK hL ν hneK).1
  have hanti : Antitone ν := (hdom ν hD).1
  have hH : ν ∈ harmSet lam :=
    harm_of lam hl hanti hcone (diracW n lam V E1 E2 hc.pair hL hc.ch1 hc.ch2 ν hne)
  obtain ⟨E', e, T', σ', F, χ, s, he, -, hF, hder, -, -, -, hb⟩ := lefData n lam hl E T hT
  have hneF : hw F ν ≠ ⊥ := by
    intro h0
    have ht := (hb ν fun a b hab => add_lt_add_of_le_of_lt (hanti hab.le) (hρ hab)).1
    rw [← (harmDom n lam hl ν hH).2, aux₃ n ν hD, h0, trOn_bot, mul_one] at ht
    exact pow_ne_zero n two_ne_zero ht.symm
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hneF
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).1 hneK
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ
    (show (⟨x, hx⟩ : hw F ν) ≠ 0 from fun h => hx0 (congrArg Subtype.val h))
  obtain ⟨t, ht, htφ, -⟩ := homSurj n E'.V V F (kF E1 E2) hF hK hL ν (f.smulRight (⟨y, hy⟩ : hw (kF E1 E2) ν))
  have htx : t x = y := by
    have := htφ ⟨x, hx⟩
    simpa [hf] using this
  have hg := ((derAt n V σ (kF E1 E2) hc.der).2 E'.V σ' F hder t).2 ht
  have hu : t ∘ₗ e.toLinearMap ∈ invA σ E := fun k ξ => by
    show t (e (ξ ∘L E.ρ k⁻¹)) = σ k (t (e ξ))
    rw [he, hg]
  refine (Submodule.ne_bot_iff _).2 ⟨y, ?_, hy0⟩
  refine Submodule.mem_iSup_of_mem ⟨_, hu⟩ ⟨e.symm x, ?_⟩
  show t (e (e.symm x)) = y
  rw [e.apply_symm_apply, htx]
