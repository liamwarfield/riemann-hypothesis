module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.WordFrameBounds.WordIdAt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.UnitaryAdjointHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupG
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.NontrivInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.HermitianConvolution.NontrivInfPf
noncomputable section

open NumberField IsDedekindDomain

attribute [local instance] FractionRing.liftAlgebra

namespace PositivityTheory.Rg.BcB.F.FBL.NontrivInfPf

lemma finrank_real_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (h : Subsingleton (InfinitePlace E)) :
    Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have hc : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 h) Fintype.card_pos
  rw [← IsCMField.card_infinitePlace_eq_card_infinitePlace] at hc
  have h1 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (maximalRealSubfield E)
  have h2 := InfinitePlace.card_add_two_mul_card_eq_rank (maximalRealSubfield E)
  have h3 := IsTotallyReal.nrComplexPlaces_eq_zero (maximalRealSubfield E)
  omega

lemma surj_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  have hbot : (⊤ : Subalgebra ℚ F) = ⊥ :=
    Subalgebra.finrank_eq_one_iff.1 (by rw [Subalgebra.topEquiv.toLinearEquiv.finrank_eq]; exact h)
  have hx : (x : F) ∈ (⊥ : Subalgebra ℚ F) := hbot ▸ Algebra.mem_top
  obtain ⟨q, hq⟩ := Algebra.mem_bot.1 hx
  have hint : IsIntegral ℤ q := by
    have : IsIntegral ℤ (x : F) := x.isIntegral_coe
    rwa [← hq, isIntegral_algebraMap_iff ] at this
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, ?_⟩
  apply RingOfIntegers.ext
  rw [← hq, ← hn]
  simp

lemma fu_of_finrank_one (F : Type) [Field F] [NumberField F] (h : Module.finrank ℚ F = 1) :
    Algebra.FormallyUnramified ℤ (𝓞 F) :=
  Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 F)) (surj_of_finrank_one F h)

theorem main (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hnt
  rw [not_nontrivial_iff_subsingleton] at hnt
  have hF := finrank_real_eq_one E hnt
  have : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) := fu_of_finrank_one _ hF
  have hunr : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt ℤ w.asIdeal := fun w => by
    have := hU w
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime w.asIdeal)
  have htop : differentIdeal ℤ (𝓞 E) = ⊤ := by
    by_contra hne
    obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
    have hPne : P ≠ ⊥ := fun h => differentIdeal_ne_bot (A := ℤ) (B := 𝓞 E) (eq_bot_iff.2 (h ▸ hle))
    let w : HeightOneSpectrum (𝓞 E) := ⟨P, hPmax.isPrime, hPne⟩
    have := (not_dvd_differentIdeal_iff (A := ℤ) (P := w.asIdeal)).2 (hunr w)
    exact this (Ideal.dvd_iff_le.2 hle)
  have hd := absNorm_differentIdeal E (𝓞 E)
  rw [htop, Ideal.absNorm_top] at hd
  have hrank : 1 < Module.finrank ℚ E := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank E
    have h2 := IsTotallyComplex.nrRealPlaces_eq_zero E
    have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    have h4 : 0 < Fintype.card (InfinitePlace E) := Fintype.card_pos
    omega
  have h2 := abs_discr_gt_two hrank
  have h1 : |discr E| = 1 := by rw [Int.abs_eq_natAbs, ← hd]; rfl
  omega

end PositivityTheory.Rg.BcB.F.FBL.NontrivInfPf

namespace PositivityTheory.Rg.BcB.F.FBL

theorem nontrivInf : NontrivInf := fun E _ _ _ hU => NontrivInfPf.main E hU

end PositivityTheory.Rg.BcB.F.FBL

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

open PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace PositivityTheory.Rg.BcB.F.B3

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PTop

section Generic

variable {ι : Type} [Fintype ι] [Nonempty ι] {H : ι → Type} [∀ s, NormedAddCommGroup (H s)]
  [∀ s, InnerProductSpace ℂ (H s)] [∀ s, CompleteSpace (H s)] {d : ℕ} {Γ : Type}

theorem wdVal_snd (gen : Γ → Prod' H d) (w : List (Γ × Bool)) :
    (wdVal gen w).2 = wdVal (fun x => (gen x).2) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, Prod.snd_mul] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp

theorem wdVal_fst (gen : Γ → Prod' H d) (w : List (Γ × Bool)) (s : ι) :
    (wdVal gen w).1 s = wdVal (fun x => (gen x).1 s) w := by
  induction w with
  | nil => simp [wdVal]
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons, Prod.fst_mul, Pi.mul_apply] at ih ⊢
    rw [ih]
    congr 1
    split_ifs <;> simp

theorem gBound_words (gen : Γ → Prod' H d) (a₀ : Γ) (β : ∀ s, H s →L[ℂ] H s) (m : ℕ)
    (u : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))
    (hu : ∀ x, Commute u (gen x).2 ∧ Commute u (star (gen x).2))
    (hW : ∀ (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (Γ × Bool)), ∃ t : ι → ℕ → ℂ,
      (∀ k, 1 ≤ k → ∑ f : Fin k → J, (∏ i, c (f i)) *
        LinearMap.trace ℂ _ ((u ^ k * wdVal (fun x => (gen x).2) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)) :
          EuclideanSpace ℂ (Fin d) →ₗ[ℂ] EuclideanSpace ℂ (Fin d)) = ∑ s, t s k) ∧
      ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ k, 1 ≤ k →
        ‖t s k‖ ≤ C * (1 + k) ^ N * ‖(β s ^ m * ∑ j, c j • wdVal (fun x => (gen x).1 s) (w j)) ^ k‖) :
    GBound gen a₀ β m u := by
  intro a ha _
  obtain ⟨J, _, c, w, L, -, rfl, hpow⟩ := adjWords _ _ gen a ha
  obtain ⟨t, ht, hb⟩ := hW J c w
  refine SG.boundAt_of β m u _ t 0 ?_ ?_
  · have hc : Commute u (∑ j, c j • wdVal gen (w j)).2 := by
      rw [Prod.snd_sum]
      refine Commute.sum_right _ _ _ fun j _ => ?_
      rw [Prod.smul_snd]
      refine Commute.smul_right ?_ _
      rw [wdVal_snd]
      refine Commute.list_prod_right _ _ fun y hy => ?_
      obtain ⟨p, -, rfl⟩ := List.mem_map.1 hy
      split_ifs
      · exact (hu p.1).2
      · exact (hu p.1).1
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [← ht k hk]
    unfold SG.trU
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc.mul_pow, ← Prod.pow_snd, hpow, Prod.snd_sum, Finset.mul_sum, ContinuousLinearMap.coe_sum, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Prod.smul_snd, mul_smul_comm, ContinuousLinearMap.coe_smul, map_smul, smul_eq_mul, wdVal_snd]
  · intro s
    obtain ⟨C, N, hC⟩ := hb s
    have e : (∑ j, c j • wdVal gen (w j)).1 s = ∑ j, c j • wdVal (fun x => (gen x).1 s) (w j) := by
      rw [Prod.fst_sum, Finset.sum_apply]
      simp only [Prod.smul_fst, Pi.smul_apply, wdVal_fst]
    exact ⟨C, N, by
      filter_upwards [eventually_ge_atTop 1] with k hk
      rw [e, Nat.sub_zero]
      exact hC k hk⟩

end Generic

theorem map_ofFn' {α β : Type} {k : ℕ} (g : α → β) (h : Fin k → α) :
    (List.ofFn h).map g = List.ofFn (fun i => g (h i)) := by
  rw [List.map_ofFn]; rfl

theorem bgen_adj {E : Type} [Field E] [NumberField E] [IsCMField E] (B : Block E) (g : BGen B) (hg : g.Ok) :
    g.adj.Ok ∧ g.adj.op = star g.op := by
  rcases g with c | t
  · refine ⟨trivial, ?_⟩
    show (starRingEnd ℂ c) • (1 : B.Hb →L[ℂ] B.Hb) = star (c • (1 : B.Hb →L[ℂ] B.Hb))
    rw [star_smul, star_one]
    rfl
  · have := BlockFiniteConvolution.blkOp₀ E B t t hg hg
    exact ⟨this.2.2.2.2.1, by rw [ContinuousLinearMap.star_eq_adjoint]; exact this.2.2.2.2.2.1⟩

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {hR : Rd.ReadLimit} {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S}
  (F : RunFrame F₀ T)

theorem good_notin_B {w : Pl E} (hw : F.d.Good w) : w ∉ F.d.B := by
  obtain ⟨-, hT, hS, hB, -⟩ := hw
  simp [LocData.B, hT, hS, hB]

theorem ug_ok (x : F.Γ) : (F.ug x).Ok F₀.Sec F.d.B := by
  rcases x with _ | x | x
  · exact trivial
  · exact trivial
  · exact ⟨x.1.2.1, good_notin_B F x.1.2.2, GlobalTheory.CompanionTheory.MatchWord.isHecke_hU F.d F.ok (if_pos x.1.2.2.1) x.2.1⟩

theorem u_word (hE : GlobalTheory.BCT.Unr E) (w : List (F.Γ × Bool)) :
    wdVal (fun x => F.R.op (F.ug x)) w = ((w.map (ul F)).map F.R.op).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b
    · simp [ul]
    · simp only [ul, if_true]
      exact (U.unitary_adjoint_holds E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x)
        (ug_ok F x)).2.symm

theorem b_word (hS : F.Struct) (i : F₀.C.ι) (w : List (F.Γ × Bool)) :
    wdVal (fun x => (F.g x i).op) w = ((w.map (gl F i)).map BGen.op).prod := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    simp only [wdVal, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    congr 1
    obtain ⟨x, b⟩ := p
    cases b
    · simp [gl]
    · simp only [gl, if_true]
      exact (bgen_adj _ _ (hS.ok x i)).2.symm

theorem bw_ok (hS : F.Struct) (i : F₀.C.ι) (w : List (F.Γ × Bool)) : ∀ g ∈ bw F i w, g.Ok := by
  intro g hg
  simp only [bw, List.mem_append, List.mem_replicate, List.mem_map] at hg
  rcases hg with ⟨-, rfl⟩ | ⟨p, -, rfl⟩
  · exact hS.βok i
  · obtain ⟨x, b⟩ := p
    cases b
    · exact hS.ok x i
    · exact (bgen_adj _ _ (hS.ok x i)).1

theorem bw_prod (i : F₀.C.ι) (w : List (F.Γ × Bool)) :
    ((bw F i w).map BGen.op).prod = (F.β i).op ^ F.m * ((w.map (gl F i)).map BGen.op).prod := by
  simp only [bw, List.map_append, List.map_replicate, List.prod_append, List.prod_replicate]
  rfl

theorem hW_frame (hE : GlobalTheory.BCT.Unr E) (hS : F.Struct) [Nontrivial (InfinitePlace E)] (hw : WordIdAt F)
    (J : Type) [Fintype J] (c : J → ℂ) (w : J → List (F.Γ × Bool)) :
    ∃ t : F₀.C.ι → ℕ → ℂ,
      (∀ k, 1 ≤ k → ∑ f : Fin k → J, (∏ i, c (f i)) *
        LinearMap.trace ℂ _ ((F.R.u ^ k * wdVal (fun x => F.R.op (F.ug x)) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
          EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) = ∑ s, t s k) ∧
      ∀ s, ∃ (C : ℝ) (N : ℕ), ∀ k, 1 ≤ k →
        ‖t s k‖ ≤ C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖ := by
  obtain ⟨cc, c₀, hc₀, hid⟩ := hw
  refine ⟨fun s k => cc s * ∑ f : Fin k → J, (∏ i, c (f i)) * BGen.sc (List.ofFn fun l => bw F s (w (f l))).flatten *
      ellSum2 (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
        (trM (BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun l => bw F s (w (f l))).flatten) (F.t₂ s)).Φ (MM F s)), ?_, ?_⟩
  · intro k hk
    have key : ∀ f : Fin k → J, LinearMap.trace ℂ _ ((F.R.u ^ k *
        wdVal (fun x => F.R.op (F.ug x)) (List.ofFn fun i => w (f i)).flatten :
          EuclideanSpace ℂ (Fin F.R.d) →L[ℂ] EuclideanSpace ℂ (Fin F.R.d)) :
          EuclideanSpace ℂ (Fin F.R.d) →ₗ[ℂ] EuclideanSpace ℂ (Fin F.R.d)) =
        ∑ s, cc s * (BGen.sc (List.ofFn fun l => bw F s (w (f l))).flatten *
          ellSum2 (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
            (trM (BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun l => bw F s (w (f l))).flatten) (F.t₂ s)).Φ (MM F s))) := by
      intro f
      have hne : (List.ofFn fun i => w (f i)) ≠ [] := by
        rw [Ne, List.ofFn_eq_nil_iff]; omega
      have e := (hid _ hne).2
      rw [List.length_ofFn] at e
      unfold tw at e
      simp only [map_ofFn'] at e
      rw [u_word F hE]
      exact e
    refine (Finset.sum_congr rfl fun f _ => by rw [key f, Finset.mul_sum]).trans ?_
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun f _ => ?_
    ring
  · intro s
    have := F₀.C.hG (F₀.C.a s)
    have := F₀.C.hG (n - F₀.C.a s)
    obtain ⟨C, N, hC⟩ := BlockFiniteConvolution.blkGrowth₁ E (F.B s) (F₀.C.μG (F₀.C.a s)) (F₀.C.μG (n - F₀.C.a s))
      ((F₀.A s).growth F.κ) (MM F s) (F.t₁ s) (F.t₂ s) J c (fun j => bw F s (w j)) (c₀ s) (hc₀ s)
      (hS.tok s).1 (hS.tok s).2 (fun j => bw_ok F hS s (w j))
    refine ⟨‖cc s‖ * C, N, fun k hk => ?_⟩
    have adm : ∀ f : Fin k → J, ∀ t, t = BGen.wd (Sum.inr (F.t₁ s) :: (List.ofFn fun i => bw F s (w (f i))).flatten) (F.t₂ s) →
        D4.IsTest2J (trM t.Φ (MM F s)) (c₀ s * (1 + t.T) + t.r) := by
      intro f t ht
      have hne : (List.ofFn fun i => w (f i)) ≠ [] := by
        rw [Ne, List.ofFn_eq_nil_iff]; omega
      have e := (hid _ hne).1 s
      unfold tw at e
      rw [map_ofFn'] at e
      subst ht
      exact e
    have hb := hC k adm
    have hsum : ∑ j, c j • ((bw F s (w j)).map BGen.op).prod =
        (F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_smul_comm, bw_prod, b_word F hS s (w j)]
    rw [hsum] at hb
    calc ‖cc s * _‖ = ‖cc s‖ * ‖_‖ := norm_mul _ _
      _ ≤ ‖cc s‖ * (C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖) :=
          mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = ‖cc s‖ * C * (1 + k) ^ N * ‖((F.β s).op ^ F.m * ∑ j, c j • wdVal (fun x => (F.g x s).op) (w j)) ^ k‖ := by
          ring

end Frame

end PTop

theorem frameBound_of (h : WordId) : FrameBound := by
  intro hR hD E _ _ _ hE n hn π hπ S T F₀ F hS
  have := FBL.nontrivInf E hE
  have hw := h hR E hE n hn π S T F₀ F hS
  show GBound _ _ _ _ _
  exact PTop.gBound_words _ _ _ _ _ (fun x => (F.toGenIn hD hS).ucomm x)
    (fun J _ c w => PTop.hW_frame F hE hS hw J c w)

end PositivityTheory.Rg.BcB.F.B3

end
