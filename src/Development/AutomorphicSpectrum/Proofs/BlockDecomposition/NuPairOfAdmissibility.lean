module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TsumMeas
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothingFundamentalDomainIntegral

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair

namespace GlobalTheory.CompanionTheory.BZNuPair

theorem whit2_isSubquotient_whitImg_top {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X : Type} [AddCommGroup X]
    [Module ℂ X] (J : Representation ℂ (Levi k fun a => Fin (d a)) X) :
    IsSubquotient (whit2 ψ d J) (whitImg ψ d J ⊤).toRepresentation := by
  let f : (whitImg ψ d J ⊤).toRepresentation.IntertwiningMap (whit2 ψ d J) :=
    ⟨(whitImg ψ d J ⊤).toSubmodule.subtype, fun _ => rfl⟩
  refine .of_surjective f fun w => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  exact ⟨⟨Submodule.Quotient.mk x, x, trivial, rfl⟩, rfl⟩

theorem not_isSubquotient_whitImg_bot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) {X W : Type} [AddCommGroup X]
    [Module ℂ X] [AddCommGroup W] [Module ℂ W] (J : Representation ℂ (Levi k fun a => Fin (d a)) X)
    {σ : Representation ℂ (GL (Fin (d 0)) k) W} (hσ : σ.IsIrreducible) :
    ¬ IsSubquotient σ (whitImg ψ d J ⊥).toRepresentation := by
  rintro ⟨R, f, hf⟩
  have := nontrivial_of_irreducible hσ
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf w
  have hv : v = 0 := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨t, ht, h⟩ := v.1.2
    have ht0 : t = 0 := ht
    rw [← h, ht0]
    simp
  exact hw (by rw [hv, map_zero])

theorem exists_constituent_of_whit2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  intro k _ _ _ _ ψ _ d X _ _ J hs hfl S hS
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded J).1 hfl
  obtain ⟨T, hT, hmin⟩ := WellFounded.has_min hlt
    {T : Subrepresentation J | IsSubquotient S.ρ (whitImg ψ d J T).toRepresentation}
    ⟨⊤, hS.trans (whit2_isSubquotient_whitImg_top ψ d J)⟩
  have hne : T ≠ ⊥ := by
    rintro rfl
    exact not_isSubquotient_whitImg_bot ψ d J S.irr hT
  obtain ⟨T', hT'lt, hmax⟩ := WellFounded.has_min hgt {U : Subrepresentation J | U < T}
    ⟨⊥, bot_lt_iff_ne_bot.2 hne⟩
  have hcov : T' ⋖ T := ⟨hT'lt, fun c h1 h2 => hmax c h2 h1⟩
  have hq : IsSubquotient (subQuot T T') J :=
    ⟨T, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.mkQ_surjective _⟩
  let τ : IrrRep (Levi k fun a => Fin (d a)) :=
    ⟨_, subQuot T T', hq.isSmooth hs, isIrreducible_subQuot hcov⟩
  obtain ⟨s, ⟨Φ⟩⟩ := GlobalTheory.LeviFactor.exists_equiv_piTensor_levi GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k (Fin 2)
    (fun a => Fin (d a)) τ
  have hspan := GlobalTheory.T.whittaker_subquotient_equiv k ψ d X J T T' (fun a => (s a).V) (fun a => (s a).ρ) hT'lt.le Φ
  refine ⟨s, (IsSubquotient.of_surjective Φ.toIntertwiningMap Φ.surjective).trans hq, ?_⟩
  rcases GlobalTheory.T.irreducible_subquotient_of_extension _ _ _ (whit2 ψ d J) S.ρ _ _ (whitImg_mono ψ d J hT'lt.le) S.irr hT with h | h
  · exact absurd hT'lt (hmin T' h)
  · obtain ⟨e⟩ := GlobalTheory.T.subquotient_equiv_of_irreducible_image _ _ _ _ (s 0).ρ _ S.ρ (s 0).irr S.irr hspan h
    exact ⟨e.symm⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensorStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_two_block_subquotient_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | exact GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.DerivQuot

section Mat

variable (k : Type) [Field k]

noncomputable def eIter (n : ℕ) : (j : ℕ) → GL (Fin n) k →* Mir k (n + j)
  | 0 => levi k n
  | j + 1 => ((levi k (n + j + 1)).comp (Mir k (n + j)).subtype).comp (eIter n j)

theorem glEmbMat_apply (m : ℕ) (A : Matrix (Fin m) (Fin m) k) (a b : Fin (m + 1)) :
    glEmbMat k m A a b = if h : (a : ℕ) < m ∧ (b : ℕ) < m then A ⟨a, h.1⟩ ⟨b, h.2⟩
      else if (a : ℕ) = b then 1 else 0 := by
  induction a using Fin.lastCases with
  | last =>
    induction b using Fin.lastCases with
    | last => simp [glEmbMat]
    | cast b =>
      have hb := b.isLt
      simp [glEmbMat, hb.ne']
  | cast a =>
    induction b using Fin.lastCases with
    | last =>
      have ha := a.isLt
      simp [glEmbMat, ha.ne]
    | cast b => simp [glEmbMat]

theorem eIter_apply (n : ℕ) : ∀ (j : ℕ) (g : GL (Fin n) k) (a b : Fin (n + j + 1)),
    (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) : Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b =
      if h : (a : ℕ) < n ∧ (b : ℕ) < n then (g : Matrix (Fin n) (Fin n) k) ⟨a, h.1⟩ ⟨b, h.2⟩
        else if (a : ℕ) = b then 1 else 0
  | 0, g, a, b => glEmbMat_apply k n _ a b
  | j + 1, g, a, b => by
    have e : (((eIter k n (j + 1) g : Mir k (n + (j + 1))) : GL (Fin (n + (j + 1) + 1)) k) :
        Matrix (Fin (n + (j + 1) + 1)) (Fin (n + (j + 1) + 1)) k) a b =
        glEmbMat k (n + j + 1) (((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) :
          Matrix (Fin (n + j + 1)) (Fin (n + j + 1)) k) a b := rfl
    rw [e, glEmbMat_apply]
    by_cases h : (a : ℕ) < n + j + 1 ∧ (b : ℕ) < n + j + 1
    · rw [dite_eq_left h, eIter_apply n j g]
    · rw [dite_eq_right h]
      have h' : ¬ ((a : ℕ) < n ∧ (b : ℕ) < n) := fun h2 => h ⟨by omega, by omega⟩
      rw [dite_eq_right h']

theorem eIter_eq_leviEmb (n j : ℕ) (hd : ∑ a, (![n, j + 1] a) = n + j + 1) (g : GL (Fin n) k) :
    ((eIter k n j g : Mir k (n + j)) : GL (Fin (n + j + 1)) k) =
      leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g) := by
  set e := stdBlocks ![n, j + 1] hd with he
  have h0 : ∀ i : Fin n, (e ⟨0, i⟩ : ℕ) = i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 0 i
    simpa using this
  have h1 : ∀ i : Fin (j + 1), (e ⟨1, i⟩ : ℕ) = n + i := fun i => by
    have := stdBlocks_val ![n, j + 1] hd 1 i
    simpa using this
  have hsplit₀ : ∀ (a : Fin 2) (i : Fin (![n, j + 1] a)), (∃ l : Fin n, e ⟨a, i⟩ = e ⟨0, l⟩) ∨
      (∃ l : Fin (j + 1), e ⟨a, i⟩ = e ⟨1, l⟩) :=
    Fin.forall_fin_two.2 ⟨fun i => Or.inl ⟨i, rfl⟩, fun i => Or.inr ⟨i, rfl⟩⟩
  have hsplit : ∀ x : Fin (n + j + 1), (∃ i : Fin n, x = e ⟨0, i⟩) ∨ (∃ i : Fin (j + 1), x = e ⟨1, i⟩) := by
    intro x
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
    exact hsplit₀ a i
  have hv0 : ∀ (i : Fin n) (h : (e ⟨0, i⟩ : ℕ) < n), (⟨(e ⟨0, i⟩ : ℕ), h⟩ : Fin n) = i := fun i _ => Fin.ext (h0 i)
  apply Units.ext
  ext x y
  rw [eIter_apply]
  rcases hsplit x with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;> rcases hsplit y with ⟨l, rfl⟩ | ⟨l, rfl⟩
  · have hi := i.isLt
    have hl := l.isLt
    rw [dite_eq_left ⟨by rw [h0]; exact hi, by rw [h0]; exact hl⟩]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 0 i l
    rw [this]
    have h2 : (firstEmb ![n, j + 1] g) 0 = g := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 0 = g
      exact Pi.mulSingle_eq_same _ _
    rw [h2, hv0, hv0]
  · have hi := i.isLt
    rw [dite_eq_right (fun h => by have := h.2; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 0) (b := 1) (by decide) i l).symm
  · have hl := l.isLt
    rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega), ite_eq_right (by rw [h0, h1]; omega)]
    exact (leviEmb_apply_ne k e _ (a := 1) (b := 0) (by decide) i l).symm
  · rw [dite_eq_right (fun h => by have := h.1; rw [h1] at this; omega)]
    have := leviEmb_apply_same k e (firstEmb ![n, j + 1] g) 1 i l
    rw [this]
    have h3 : (firstEmb ![n, j + 1] g) 1 = 1 := by
      show (Pi.mulSingle (0 : Fin 2) g : ∀ a, GL (Fin (![n, j + 1] a)) k) 1 = 1
      exact Pi.mulSingle_eq_of_ne (by decide) _
    rw [h3, h1, h1]
    by_cases hil : i = l
    · subst hil
      exact (ite_eq_left rfl).trans (Matrix.one_apply_eq i).symm
    · have : ¬ (n + (i : ℕ) = n + l) := fun h => hil (Fin.ext (by omega))
      rw [ite_eq_right this]
      exact (Matrix.one_apply_ne hil).symm

end Mat

section Quot

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem comap_twKer_phiMinus (ψ : AddChar k Circle) {m n : ℕ} (hnm : n ≤ m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Mir k (m + 1)) V) :
    (twKer (phiMinus k ψ τ) (derUnipM k m n) (derCharM k ψ m n)).comap
        (twKer τ (MirUin k (m + 1)) (mirChar k ψ m)).mkQ =
      twKer τ (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n) := by
  have twKer_eq_map {G M W : Type} [Group G] [Group M] [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ G W) (N₁ : Subgroup G) (θ₁ : N₁ →* ℂˣ) (s : M →* G)
      (hs : ∀ (m : M) (n : N₁), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N₁, θ₁ ⟨_, h⟩ = θ₁ n)
      (N₂ : Subgroup M) (θ₂ : N₂ →* ℂˣ) (N : Subgroup G) (θ : N →* ℂˣ)
      (h1 : ∀ u : N₁, ∃ h : (u : G) ∈ N, θ ⟨u, h⟩ = θ₁ u)
      (h2 : ∀ a : N₂, ∃ h : s a ∈ N, θ ⟨s a, h⟩ = θ₂ a)
      (h3 : ∀ u : N, ∃ u₁ : N₁, ∃ a : N₂, (u : G) = u₁ * s a) :
      twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂ = (twKer ρ N θ).map (twKer ρ N₁ θ₁).mkQ ∧
        twKer ρ N₁ θ₁ ≤ twKer ρ N θ := by
    refine ⟨le_antisymm ?_ ?_, ?_⟩
    · refine Submodule.span_le.2 ?_
      rintro w ⟨a, x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        obtain ⟨h, hθ⟩ := h2 a
        refine ⟨ρ (s a) v - ((θ ⟨s a, h⟩ : ℂˣ) : ℂ) • v, Submodule.subset_span ⟨⟨_, h⟩, v, rfl⟩, ?_⟩
        rw [hθ, Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
    · rw [Submodule.map_le_iff_le_comap]
      refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨u₁, a, hu⟩ := h3 u
      obtain ⟨hu₁, e1⟩ := h1 u₁
      obtain ⟨ha, e2⟩ := h2 a
      have hθ : θ u = θ₁ u₁ * θ₂ a := by
        have : u = ⟨u₁, hu₁⟩ * ⟨s a, ha⟩ := Subtype.ext hu
        rw [this, map_mul, e1, e2]
      have hdec : ρ (u : G) v - ((θ u : ℂˣ) : ℂ) • v =
          (ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v) +
            ((θ₁ u₁ : ℂˣ) : ℂ) • (ρ (s a) v - ((θ₂ a : ℂˣ) : ℂ) • v) := by
        rw [hθ, hu, map_mul, mul_apply_eq_comp, Units.val_mul, smul_sub, mul_smul]
        abel
      have hz : ρ (u₁ : G) (ρ (s a) v) - ((θ₁ u₁ : ℂˣ) : ℂ) • ρ (s a) v ∈ twKer ρ N₁ θ₁ :=
        Submodule.subset_span ⟨u₁, _, rfl⟩
      show (twKer ρ N₁ θ₁).mkQ _ ∈ twKer (twAct ρ N₁ θ₁ s hs) N₂ θ₂
      rw [hdec, map_add (f := _), Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hz, zero_add, map_smul]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, Submodule.Quotient.mk v, ?_⟩)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
      rfl
    · refine Submodule.span_le.2 ?_
      rintro w ⟨u, v, rfl⟩
      obtain ⟨h, hθ⟩ := h1 u
      exact Submodule.subset_span ⟨⟨u, h⟩, v, by rw [hθ]⟩
  obtain ⟨e, hle⟩ := twKer_eq_map τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)
    (derUnipM k m n) (derCharM k ψ m n) (derUnipM k (m + 1) n) (derCharM k ψ (m + 1) n)
    (GlobalTheory.CompanionTheory.BZMirStep.MirUin_step ψ hnm) (GlobalTheory.CompanionTheory.BZMirStep.levi_step ψ hnm)
    (GlobalTheory.CompanionTheory.BZMirStep.derUnipM_decomp hnm)
  show (twKer (twAct τ (MirUin k (m + 1)) (mirChar k ψ m) _ (levi_stab ψ m)) (derUnipM k m n)
    (derCharM k ψ m n)).comap _ = _
  rw [e, Submodule.comap_map_eq, Submodule.ker_mkQ, sup_eq_left.2 hle]

theorem ker_comp_mkQ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (K : Submodule ℂ V)
    (L : Submodule ℂ (V ⧸ K)) (q : (V ⧸ K) →ₗ[ℂ] W) (h : LinearMap.ker q = L) :
    LinearMap.ker (q ∘ₗ K.mkQ) = L.comap K.mkQ := by
  rw [LinearMap.ker_comp, h]

theorem exists_quotM (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)),
    ∃ q : τ.V →ₗ[ℂ] TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n) ∧
      ∀ (g : GL (Fin n) k) (v : τ.V), q (τ.ρ (eIter k n j g) v) = derivM k ψ j τ g (q v) := by
  intro j
  induction j with
  | zero =>
    intro τ
    exact ⟨(twKer τ.ρ (MirUin k n) 1).mkQ, Submodule.mkQ_surjective _,
      (Submodule.ker_mkQ _).trans (GlobalTheory.CompanionTheory.BZMir.twKer_MirUin_eq_derUnipM k ψ n _ τ.ρ), fun g v => rfl⟩
  | succ j ih =>
    intro τ
    obtain ⟨q₁, hs, hk, he⟩ := ih (MRep.phiM k ψ τ)
    refine ⟨q₁ ∘ₗ (twKer τ.ρ (MirUin k (n + j + 1)) (mirChar k ψ (n + j))).mkQ,
      hs.comp (Submodule.mkQ_surjective _), ?_, fun g v => he g (Submodule.Quotient.mk v)⟩
    exact (ker_comp_mkQ _ _ q₁ hk).trans (comap_twKer_phiMinus ψ (Nat.le_add_right n j) τ.ρ)

theorem exists_deriv_quot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ (g : GL (Fin n) k) (v : V), q (π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) =
        GlobalTheory.BZMir.deriv k ψ j π g (q v) := by
  intro k _ _ _ _ ψ n j V _ _ π hd
  obtain ⟨q, hs, hk, he⟩ := exists_quotM ψ n j (resM k π)
  refine ⟨q, hs, hk.trans (GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM k ψ (n + j) n V π), fun g v => ?_⟩
  rw [← eIter_eq_leviEmb k n j hd g]
  exact he g v

end Quot

end GlobalTheory.CompanionTheory.DerivQuot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetTwistedQuotientStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_jacquet_twisted_quotient : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    ∃ q : V →ₗ[ℂ] TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1, Function.Surjective q ∧
      LinearMap.ker q = twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) ∧
      ∀ (g : GL (Fin n) k) (v : V), q (π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) =
        GlobalTheory.BZMir.deriv k ψ j π g (q v) := by
  first | exact @GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot | exact GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot | (intros; apply GlobalTheory.CompanionTheory.DerivQuot.exists_deriv_quot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquet
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquet
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair

noncomputable section

namespace GlobalTheory.CompanionTheory.BZNuPair.DerComap

section Groups

variable {k : Type} [Field k] {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

theorem stdBlocks_zero_val (i : Fin (d 0)) : (stdBlocks d h ⟨0, i⟩ : ℕ) = i := by
  simpa using stdBlocks_val d h 0 i

theorem stdBlocks_one_val (i : Fin (d 1)) : (stdBlocks d h ⟨1, i⟩ : ℕ) = d 0 + i := by
  have := stdBlocks_val d h 1 i
  simpa using this

theorem idx_cases (i : Fin N) : (∃ a : Fin (d 0), i = stdBlocks d h ⟨0, a⟩) ∨
    ∃ a : Fin (d 1), i = stdBlocks d h ⟨1, a⟩ := by
  obtain ⟨⟨c, i'⟩, rfl⟩ := (stdBlocks d h).surjective i
  have key : ∀ (c : Fin 2) (i' : Fin (d c)),
      (∃ a : Fin (d 0), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨0, a⟩) ∨
        ∃ a : Fin (d 1), stdBlocks d h ⟨c, i'⟩ = stdBlocks d h ⟨1, a⟩ :=
    Fin.forall_fin_two.2 ⟨fun i' => Or.inl ⟨i', rfl⟩, fun i' => Or.inr ⟨i', rfl⟩⟩
  exact key c i'

theorem blk_two (i : Fin N) : blk (stdBlocks d h) i = if (i : ℕ) < d 0 then 0 else 1 := by
  rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [blk_apply, stdBlocks_zero_val, if_pos a.2]
  · rw [blk_apply, stdBlocks_one_val, if_neg (by omega)]

theorem mem_unipRad_iff {g : GL (Fin N) k} :
    g ∈ unipRad k (stdBlocks d h) ↔
      ∀ i j : Fin N, ¬ ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) →
        (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  rw [GlobalTheory.RadRev.mem_unipRad_entries]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [blk_two, blk_two]
  have : ((if (i : ℕ) < d 0 then (0 : Fin 2) else 1) < if (j : ℕ) < d 0 then 0 else 1) ↔
      ((i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) := by
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] <;> omega
  rw [this]

theorem derUnip_col {n : ℕ} {w : GL (Fin N) k} (hw : w ∈ derUnip k N n) (r i : Fin N) (hi : (i : ℕ) < n) :
    (w : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i := by
  have h1 := congrFun ((Subgroup.mem_inf.1 hw).2 i hi) r
  have hc : ((w : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (w : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [hc] at h1
  rw [h1, Matrix.one_apply, Pi.single_apply]

theorem mem_derUnip_of_col {n : ℕ} {g : GL (Fin N) k} (hg : g ∈ unipB k (Fin N))
    (hc : ∀ r i : Fin N, (i : ℕ) < n →
      (g : Matrix (Fin N) (Fin N) k) r i = (1 : Matrix (Fin N) (Fin N) k) r i) :
    g ∈ derUnip k N n := by
  refine Subgroup.mem_inf.2 ⟨hg, fun i hi => ?_⟩
  ext r
  have e : ((g : Matrix (Fin N) (Fin N) k) *ᵥ Pi.single i 1) r = (g : Matrix (Fin N) (Fin N) k) r i := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e, hc r i hi, Matrix.one_apply, Pi.single_apply]

theorem unipRad_le_derUnip : unipRad k (stdBlocks d h) ≤ derUnip k N (d 0) := by
  intro g hg
  have hE := (mem_unipRad_iff d h).1 hg
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]
  · exact hE r i (by omega)

def secEmb : GL (Fin (d 1)) k →* GL (Fin N) k := (leviEmb k (stdBlocks d h)).comp (secondEmb d)

theorem secEmb_one_one (u : GL (Fin (d 1)) k) (a b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨1, b⟩) =
      (u : Matrix (Fin (d 1)) (Fin (d 1)) k) a b := by
  simp [secEmb, secondEmb]

theorem secEmb_zero_zero (u : GL (Fin (d 1)) k) (a b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨0, b⟩) =
      (1 : Matrix (Fin (d 0)) (Fin (d 0)) k) a b := by
  simp [secEmb, secondEmb]

theorem secEmb_zero_one (u : GL (Fin (d 1)) k) (a : Fin (d 0)) (b : Fin (d 1)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨0, a⟩) (stdBlocks d h ⟨1, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 0) (b := 1) (by decide) a b

theorem secEmb_one_zero (u : GL (Fin (d 1)) k) (a : Fin (d 1)) (b : Fin (d 0)) :
    (secEmb d h u : Matrix (Fin N) (Fin N) k) (stdBlocks d h ⟨1, a⟩) (stdBlocks d h ⟨0, b⟩) = 0 :=
  leviEmb_apply_ne (m := fun a => Fin (d a)) k (stdBlocks d h) (secondEmb d u) (a := 1) (b := 0) (by decide) a b

theorem secEmb_mem {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    secEmb d h u ∈ derUnip k N (d 0) := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  refine mem_derUnip_of_col ((mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩) fun r i hi => ?_
  · have hlt := Fin.lt_def.1 hji
    rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> rcases idx_cases d h j with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [secEmb_zero_zero, one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hlt
    · exact secEmb_zero_one d h u a b
    · exact secEmb_one_zero d h u a b
    · rw [secEmb_one_one]
      rw [stdBlocks_one_val, stdBlocks_one_val] at hlt
      exact u1 a b (Fin.lt_def.2 (by omega))
  · rcases idx_cases d h i with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [secEmb_zero_zero, one_apply_eq]
    · rw [secEmb_one_one, u2]
  · rcases idx_cases d h i with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rcases idx_cases d h r with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [secEmb_zero_zero]
        by_cases e : a = b
        · subst e; simp
        · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
      · rw [secEmb_one_zero, one_apply_ne]
        intro e'
        have h1 := congrArg Fin.val e'
        rw [stdBlocks_one_val, stdBlocks_zero_val] at h1
        have := b.2
        omega
    · rw [stdBlocks_one_val] at hi
      omega

theorem det_eq_one {m : ℕ} {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) :
    GeneralLinearGroup.det u = 1 := by
  obtain ⟨u1, u2⟩ := (mem_unipB k).1 hu
  ext
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular (fun i j hij => u1 i j hij)]
  simp [u2]

theorem exists_decomp {w : GL (Fin N) k} (hw : w ∈ derUnip k N (d 0)) :
    ∃ r ∈ unipRad k (stdBlocks d h), ∃ u ∈ unipB k (Fin (d 1)), w = r * secEmb d h u := by
  have hB := (mem_unipB k).1 (derUnip_le_unipB k N (d 0) hw)
  have hp : w ∈ parab k (stdBlocks d h) := by
    refine mem_parab.2 fun i j hij => ?_
    rw [blk_two, blk_two] at hij
    refine hB.1 i j (Fin.lt_def.2 ?_)
    by_cases hi : (i : ℕ) < d 0 <;> by_cases hj : (j : ℕ) < d 0 <;> simp [hi, hj] at hij
    omega
  obtain ⟨r', hr', e1⟩ := exists_levi_mul_unip k (stdBlocks d h) ⟨w, hp⟩
  set l := leviProj k (stdBlocks d h) ⟨w, hp⟩ with hl
  have hl0 : l 0 = 1 := by
    ext i j
    rw [hl, leviProj_apply]
    have := derUnip_col hw (stdBlocks d h ⟨0, i⟩) (stdBlocks d h ⟨0, j⟩)
      (by rw [stdBlocks_zero_val]; exact j.2)
    refine this.trans ?_
    rw [Units.val_one]
    by_cases e : i = j
    · subst e; simp
    · rw [one_apply_ne e, one_apply_ne fun e' => e (by simpa using e')]
  have hlsec : l = secondEmb d (l 1) := by
    have key : ∀ a, l a = secondEmb d (l 1) a :=
      Fin.forall_fin_two.2 ⟨by simp [secondEmb, hl0], by simp [secondEmb]⟩
    exact funext key
  have hu : l 1 ∈ unipB k (Fin (d 1)) := by
    refine (mem_unipB k).2 ⟨fun a c hca => ?_, fun a => ?_⟩
    · rw [hl, leviProj_apply]
      refine hB.1 _ _ (Fin.lt_def.2 ?_)
      rw [stdBlocks_one_val, stdBlocks_one_val]
      have := Fin.lt_def.1 hca
      omega
    · rw [hl, leviProj_apply]
      exact hB.2 _
  have hs : secEmb d h (l 1) = leviEmb k (stdBlocks d h) l := by
    show leviEmb k (stdBlocks d h) (secondEmb d (l 1)) = _
    rw [← hlsec]
  have e1' : w = leviEmb k (stdBlocks d h) l * r' := e1
  refine ⟨leviEmb k (stdBlocks d h) l * r' * (leviEmb k (stdBlocks d h) l)⁻¹,
    (Subgroup.mem_normalizer_iff.1 (leviEmb_mem_normalizer k (stdBlocks d h) l) r').1 hr', l 1, hu, ?_⟩
  rw [hs]
  exact e1'.trans (by group)

end Groups

section Chars

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} (d : Fin 2 → ℕ) (h : ∑ a, d a = N)

theorem derChar_eq_one_of_mem_unipRad (ψ : AddChar k Circle) (u : derUnip k N (d 0))
    (hu : (u : GL (Fin N) k) ∈ unipRad k (stdBlocks d h)) : derChar k ψ N (d 0) u = 1 := by
  have hE := (mem_unipRad_iff d h).1 hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

theorem derChar_secEmb (ψ : AddChar k Circle) (u : unipB k (Fin (d 1)))
    (hs : secEmb d h (u : GL (Fin (d 1)) k) ∈ derUnip k N (d 0)) :
    derChar k ψ N (d 0) ⟨_, hs⟩ = whitChar ψ (d 1) u := by
  show Circle.toUnits _ = Circle.toUnits _
  refine congrArg _ (congrArg _ ?_)
  symm
  refine Finset.sum_bij (fun q _ => (stdBlocks d h ⟨1, q.1⟩, stdBlocks d h ⟨1, q.2⟩)) ?_ ?_ ?_ ?_
  · intro q hq
    have := (Finset.mem_filter.1 hq).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, ?_⟩
    · simp only [stdBlocks_one_val]
      omega
    · simp only [stdBlocks_one_val]
      omega
  · rintro ⟨a, b⟩ _ ⟨a', b'⟩ _ e
    have e1 := (stdBlocks d h).injective (congrArg Prod.fst e)
    have e2 := (stdBlocks d h).injective (congrArg Prod.snd e)
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at e1 e2
    simp [e1, e2]
  · rintro ⟨p1, p2⟩ hp
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp only at h1 h2
    rcases idx_cases d h p1 with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rw [stdBlocks_zero_val] at h2
      have := a.2
      omega
    rcases idx_cases d h p2 with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · rw [stdBlocks_zero_val, stdBlocks_one_val] at h1
      have := b.2
      omega
    refine ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    rw [stdBlocks_one_val, stdBlocks_one_val] at h1
    simp only
    omega
  · intro q _
    exact (secEmb_one_one d h _ q.1 q.2).symm

theorem deltaHalf_secondEmb {u : GL (Fin (d 1)) k} (hu : u ∈ unipB k (Fin (d 1))) :
    deltaHalf k (fun a => Fin (d a)) (secondEmb d u) = 1 := by
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have key : ∀ a, GeneralLinearGroup.det ((secondEmb d u : Levi k fun a => Fin (d a)) a) = 1 :=
    Fin.forall_fin_two.2 ⟨by simp [secondEmb], by simpa [secondEmb] using det_eq_one hu⟩
  rw [key, map_one]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem twKer_unipRad_le (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    twKer π (unipRad k (stdBlocks d h)) 1 ≤ twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  refine Submodule.span_mono ?_
  rintro _ ⟨u, v, rfl⟩
  refine ⟨⟨u, unipRad_le_derUnip d h u.2⟩, v, ?_⟩
  rw [derChar_eq_one_of_mem_unipRad d h ψ _ u.2]
  simp

theorem jac_secondEmb (π : Representation ℂ (GL (Fin N) k) V) {u : GL (Fin (d 1)) k}
    (hu : u ∈ unipB k (Fin (d 1))) (v : V) :
    GlobalTheory.SmGL.jac (stdBlocks d h) π (secondEmb d u) (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (π (secEmb d h u) v) := by
  rw [jac_mk, deltaHalf_secondEmb d hu]
  simp [secEmb]

theorem whitKer_jac_eq_map (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    whitKer ψ d (GlobalTheory.SmGL.jac (stdBlocks d h) π) =
      (twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0))).map
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨u, x, rfl⟩
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ x
    have hs := secEmb_mem d h u.2
    refine ⟨π (secEmb d h u) v - (whitChar ψ (d 1) u : ℂ) • v,
      Submodule.subset_span ⟨⟨_, hs⟩, v, ?_⟩, ?_⟩
    · rw [derChar_secEmb d h ψ u hs]
    · rw [map_sub, map_smul]
      exact congrArg₂ _ (jac_secondEmb d h π u.2 v).symm rfl
  · refine Submodule.map_le_iff_le_comap.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨w, hw⟩, v, rfl⟩
    obtain ⟨r, hr, u, hu, rfl⟩ := exists_decomp d h hw
    have hs := secEmb_mem d h hu
    have hc : derChar k ψ N (d 0) ⟨_, hw⟩ = whitChar ψ (d 1) ⟨u, hu⟩ := by
      have e : (⟨_, hw⟩ : derUnip k N (d 0)) = ⟨r, unipRad_le_derUnip d h hr⟩ * ⟨_, hs⟩ := rfl
      rw [e, map_mul, derChar_eq_one_of_mem_unipRad d h ψ _ hr, one_mul]
      exact derChar_secEmb d h ψ ⟨u, hu⟩ hs
    have hr' : Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1) (π (r * secEmb d h u) v) =
        Submodule.Quotient.mk (π (secEmb d h u) v) := by
      refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨r, hr⟩, π (secEmb d h u) v, ?_⟩)
      simp
    rw [SetLike.mem_coe, Submodule.mem_comap]
    rw [hc, map_sub, map_smul, hr', ← jac_secondEmb d h π hu v]
    exact Submodule.subset_span ⟨⟨u, hu⟩, Submodule.Quotient.mk v, rfl⟩

theorem comap_whitKer_jac (ψ : AddChar k Circle) (π : Representation ℂ (GL (Fin N) k) V) :
    (whitKer ψ d (GlobalTheory.SmGL.jac (stdBlocks d h) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks d h)) 1)) =
      twKer π (derUnip k N (d 0)) (derChar k ψ N (d 0)) := by
  rw [whitKer_jac_eq_map, Submodule.comap_map_eq, Submodule.ker_mkQ]
  exact sup_eq_left.2 (twKer_unipRad_le d h ψ π)

end Chars

theorem whitKer_jac_comap_eq_twKer_derUnip : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) :=
  fun _ _ _ _ _ ψ _ _ _ _ _ π hd => comap_whitKer_jac _ hd ψ π

end GlobalTheory.CompanionTheory.BZNuPair.DerComap

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerKernelPullbackJacquetStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_kernel_pullback_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1),
    (whitKer ψ ![n, j + 1] (jac (stdBlocks ![n, j + 1] hd) π)).comap
        (Submodule.mkQ (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1)) =
      twKer π (derUnip k (n + j + 1) n) (derChar k ψ (n + j + 1) n) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | exact GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.DerComap.whitKer_jac_comap_eq_twKer_derUnip <;> assumption)
end
end

noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc GlobalTheory.CompanionTheory.BZNuPair Zc.Cos GlobalTheory.CompanionTheory.ThetaProd GlobalTheory.JHMult

namespace GlobalTheory.CompanionTheory.BZNuPair

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem deltaHalf_firstEmb (n j : ℕ) (g : GL (Fin n) k) :
    deltaHalf k (fun a => Fin (![n, j + 1] a)) (firstEmb ![n, j + 1] g) =
      detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2)) g := by
  rw [deltaHalf_apply, Fin.prod_univ_two]
  have h0 : modExp (fun a => Fin (![n, j + 1] a)) (0 : Fin 2) = (j : ℤ) + 1 := by
    have e1 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
    have e2 : (Finset.univ.filter fun b : Fin 2 => b < (0 : Fin 2)) = ∅ := by decide
    simp [modExp, e1, e2]
  have f0 : firstEmb ![n, j + 1] g (0 : Fin 2) = g :=
    Pi.mulSingle_eq_same (M := fun a => GL (Fin (![n, j + 1] a)) k) (0 : Fin 2) g
  have f1 : firstEmb ![n, j + 1] g (1 : Fin 2) = 1 :=
    Pi.mulSingle_eq_of_ne (M := fun a => GL (Fin (![n, j + 1] a)) k) (by decide : (1 : Fin 2) ≠ 0) g
  rw [h0, f0, f1, map_one, map_one, mul_one]
  simp [detChar]
  rfl

theorem equiv_of_ker {G V D Q : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup D] [Module ℂ D]
    [AddCommGroup Q] [Module ℂ Q] (ρ : Representation ℂ G D) (σ : Representation ℂ G Q) (χ : G →* ℂˣ)
    (q : V →ₗ[ℂ] D) (r : V →ₗ[ℂ] Q) (hqs : Function.Surjective q) (hrs : Function.Surjective r)
    (hk : LinearMap.ker r = LinearMap.ker q) (A : G → V → V) (hq : ∀ g v, q (A g v) = ρ g (q v))
    (hr : ∀ g v, σ g (r v) = (((χ g)⁻¹ : ℂˣ) : ℂ) • r (A g v)) : Nonempty (ρ.Equiv (GlobalTheory.SmGL.twist σ χ)) := by
  let E := (q.quotKerEquivOfSurjective hqs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hk.symm).trans (r.quotKerEquivOfSurjective hrs))
  have hE : ∀ v, E (q v) = r v := by
    intro v
    have : (q.quotKerEquivOfSurjective hqs).symm (q v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    simp only [E, LinearEquiv.trans_apply, this]
    rfl
  refine ⟨.mk E fun g => ?_⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := hqs x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [← hq, hE, hE, twist_apply, hr, smul_smul]
  rw [show ((χ g : ℂˣ) : ℂ) * ((((χ g)⁻¹ : ℂˣ) : ℂˣ) : ℂ) = 1 by rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]

set_option maxHeartbeats 1000000 in
theorem deriv_equiv (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hd : ∑ a, (![n, j + 1] a) = n + j + 1) :
    Nonempty ((GlobalTheory.BZMir.deriv k ψ j π).Equiv
      (GlobalTheory.SmGL.twist (whit2 ψ ![n, j + 1] (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π)) (detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))))) := by
  obtain ⟨q, hqs, hqk, hqg⟩ := GlobalTheory.T.derivative_jacquet_twisted_quotient k ψ n j V π hd
  have hcm := GlobalTheory.T.whittaker_kernel_pullback_jacquet k ψ n j V π hd
  refine equiv_of_ker _ _ _ q ((whitKer ψ ![n, j + 1] (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π)).mkQ ∘ₗ
      (twKer π (unipRad k (stdBlocks ![n, j + 1] hd)) 1).mkQ) hqs
    ((Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)) ?_
    (fun g v => π (leviEmb k (stdBlocks ![n, j + 1] hd) (firstEmb ![n, j + 1] g)) v) hqg ?_
  · rw [hqk, ← hcm, LinearMap.ker_comp, Submodule.ker_mkQ]
  · intro g v
    show Submodule.Quotient.mk (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π (firstEmb ![n, j + 1] g) (Submodule.Quotient.mk v)) = _
    rw [jac_mk, ← deltaHalf_firstEmb]
    rfl

theorem isSubquotient_of_comp {G H V W : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (θ : H →* G) (hθ : Function.Surjective θ)
    (h : IsSubquotient (σ.comp θ) (ρ.comp θ)) : IsSubquotient σ ρ := by
  obtain ⟨T, f, hf⟩ := h
  let T' : Subrepresentation ρ := ⟨T.toSubmodule, fun g v hv => by
    obtain ⟨c, rfl⟩ := hθ g
    exact T.apply_mem_toSubmodule c hv⟩
  refine ⟨T', .mk f.toLinearMap fun g => ?_, hf⟩
  obtain ⟨c, rfl⟩ := hθ g
  ext v
  exact f.isIntertwining _ _ c v

theorem thetaL_surjective {h : ℕ} (d : Fin h → ℕ) : Function.Surjective (thetaL (A := k) d) := by
  intro m
  let φ : ∀ a, GL (Fin (d a)) k := fun a =>
    Eq.rec (motive := fun x _ => GL (Fin (d x)) k) (m (Fin.rev a)) (Fin.rev_rev a)
  refine ⟨fun a => thetaW k (d a) (φ a), ?_⟩
  funext a
  show thetaW k (d (Fin.rev a)) (thetaW k (d (Fin.rev a)) (φ (Fin.rev a))) = m a
  rw [GlobalTheory.CompanionTheory.ThetaInv.thetaW_thetaW]
  have key : ∀ (b : Fin h) (_ : b = a) (e : Fin.rev b = Fin.rev a),
      (Eq.rec (motive := fun x _ => GL (Fin (d x)) k) (m b) e : GL (Fin (d (Fin.rev a))) k) = m a := by
    rintro b rfl e
    rfl
  exact key _ (Fin.rev_rev a) _


set_option maxHeartbeats 1000000 in
theorem jm_contra_gen (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (u : Fin h → IrrGL (k := k))
    (hd : ∑ a, (u a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (H : jm u hd (contra π) ≠ 0) : jm (dualRev hA u) (sum_dualRev hA u hd) π ≠ 0 := by
  have hGK := GlobalTheory.CompanionTheory.GKLocalProof.gkLocal (k := k) hA
  obtain ⟨E1⟩ := GlobalTheory.CompanionTheory.ThetaW.comp_thetaW_equiv_contra hGK N π hs hi
  have h1 : jm u hd (π.comp (thetaW k N)) ≠ 0 := by
    rwa [GlobalTheory.CompanionTheory.JacquetCongr.jm_congr_of_equiv u hd _ _ ⟨E1⟩]
  have h2 := jhMult_ne_zero_iff.1 h1
  have hd' : ∑ a, (u (Fin.rev a)).1 = N := sum_dualRev hA u hd
  obtain ⟨E2⟩ := GlobalTheory.T.jacquet_theta_reverse_blocks k h N (fun a => (u a).1) hd hd' V π
  have h3 := h2.trans (IsSubquotient.of_injective E2.toIntertwiningMap E2.injective)
  have T1 := piTensorRevEquiv (fun a => (u a).rep)
  have T2 := compEquiv (piTensorEquiv fun a => blockEquiv hA hGK u a) (revPi fun a => GL (Fin (u a).1) k)
  have T3 := equivOfEq (piTensor_comp_thetaL (k := k) (fun a => (u a).1) fun a => (dualRev hA u a).rep)
  have TT := (T1.trans T2).trans T3
  have h4 := (IsSubquotient.of_surjective TT.toIntertwiningMap TT.surjective).trans h3
  exact jhMult_ne_zero_iff.2 (isSubquotient_of_comp _ (thetaL_surjective _) h4)

theorem jm_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (x y : IrrGL (k := k))
    (hd : ∑ a, (![x, y] a).1 = N) (h : 1 ≤ jm ![x, y] hd (contra π)) :
    ∃ hd' : ∑ a, (![dualCl y, dualCl x] a).1 = N, 1 ≤ jm ![dualCl y, dualCl x] hd' π := by
  have h6 := jm_contra_gen hA ![x, y] hd π hs hi (ENat.one_le_iff_ne_zero.1 h)
  have key : ∀ (u w : Fin 2 → IrrGL (k := k)), u = w → ∀ hu : ∑ a, (u a).1 = N, jm u hu π ≠ 0 →
      ∃ hw : ∑ a, (w a).1 = N, 1 ≤ jm w hw π := by
    rintro u _ rfl hu h
    exact ⟨hu, ENat.one_le_iff_ne_zero.2 h⟩
  refine key _ _ ?_ _ h6
  rw [dualRev_eq]
  funext a
  fin_cases a <;> rfl

theorem isSubquotient_twist {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} (h : IsSubquotient σ ρ) (χ : G →* ℂˣ) :
    IsSubquotient (GlobalTheory.SmGL.twist σ χ) (GlobalTheory.SmGL.twist ρ χ) := by
  obtain ⟨T, f, hf⟩ := h
  let T' : Subrepresentation (GlobalTheory.SmGL.twist ρ χ) := ⟨T.toSubmodule, fun g v hv => by
    rw [twist_apply]
    exact T.toSubmodule.smul_mem _ (T.apply_mem_toSubmodule g hv)⟩
  refine ⟨T', .mk f.toLinearMap fun g => ?_, hf⟩
  ext v
  have e : T'.toRepresentation g v = ((χ g : ℂˣ) : ℂ) • T.toRepresentation g v :=
    Subtype.ext (by simp [twist_apply]; rfl)
  have h2 := f.isIntertwining _ _ g v
  simp only [LinearMap.comp_apply, twist_apply, LinearMap.smul_apply]
  erw [e]
  rw [map_smul]
  erw [h2]
  rfl

theorem isSubquotient_untwist {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ G W} {ρ : Representation ℂ G V} {χ χ' : G →* ℂˣ} (h : IsSubquotient σ (GlobalTheory.SmGL.twist ρ χ))
    (hm : χ' * χ = 1) : IsSubquotient (GlobalTheory.SmGL.twist σ χ') ρ := by
  have h2 := isSubquotient_twist h χ'
  have e : GlobalTheory.SmGL.twist (GlobalTheory.SmGL.twist ρ χ) χ' = ρ := by
    ext g v
    have : ((χ' g : ℂˣ) : ℂ) * ((χ g : ℂˣ) : ℂ) = 1 := by
      have := congrArg (fun f : G →* ℂˣ => ((f g : ℂˣ) : ℂ)) hm
      simpa using this
    simp [twist_apply, smul_smul, this]
  rwa [e] at h2

theorem sumTwo (n j : ℕ) : ∑ a, (![n, j + 1] a) = n + j + 1 := by
  simp [Fin.sum_univ_two]; omega

theorem deriv_irr_sub (ψ : AddChar k Circle) (hc : Continuous ψ) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k n) 1)) :
    ∃ (S : IrrRep (GL (Fin n) k)) (f : S.ρ.IntertwiningMap (GlobalTheory.BZMir.deriv k ψ j π)), Function.Injective f := by
  have hd := sumTwo n j
  obtain ⟨E⟩ := deriv_equiv ψ n j π hd
  have hJs := isSmooth_jac (stdBlocks ![n, j + 1] hd) hs
  have hJf : HasFiniteLength (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 (Fin 2) (Fin (n + j + 1)) (fun a => Fin (![n, j + 1] a)) (stdBlocks ![n, j + 1] hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  have hnt' : Nontrivial (_ ⧸ whitKer ψ ![n, j + 1] (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π)) :=
    E.toLinearEquiv.symm.toEquiv.nontrivial
  obtain ⟨S, f, hf⟩ := GlobalTheory.T.whittaker_two_block_injective_irreducible k ψ hc ![n, j + 1] _ _ hJs hJf hnt'
  let χ := detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))
  have hχ : IsSmoothChar χ := (isSmoothChar_absPow _).detChar
  refine ⟨irrTwist S χ hχ, E.symm.toIntertwiningMap.comp (twistMap f χ), ?_⟩
  exact E.symm.injective.comp hf

theorem deriv_jm (ψ : AddChar k Circle) (hc : Continuous ψ) (n j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (n + j + 1)) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (S : IrrRep (GL (Fin n) k)) (hS : IsSubquotient S.ρ (GlobalTheory.BZMir.deriv k ψ j π)) :
    ∃ (y : IrrGL (k := k)) (hd : ∑ a, (![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), y] a).1 = n + j + 1),
      y.1 = j + 1 ∧ 1 ≤ jm ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), y] hd π := by
  have hd := sumTwo n j
  obtain ⟨E⟩ := deriv_equiv ψ n j π hd
  have hJs := isSmooth_jac (stdBlocks ![n, j + 1] hd) hs
  have hJf : HasFiniteLength (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 (Fin 2) (Fin (n + j + 1)) (fun a => Fin (![n, j + 1] a)) (stdBlocks ![n, j + 1] hd) V π hs
      (hasFiniteLength_of_isIrreducible hi)
  let χ := detChar (Fin n) (absPow k (((j : ℂ) + 1) / 2))
  let χ' := detChar (Fin n) (absPow k (-(((j : ℂ) + 1) / 2)))
  have hχ' : IsSmoothChar χ' := (isSmoothChar_absPow _).detChar
  have hmul : χ' * χ = 1 := by
    ext g
    simp [χ, χ', detChar, absPow_neg]
  have h1 : IsSubquotient S.ρ (GlobalTheory.SmGL.twist (whit2 ψ ![n, j + 1] (GlobalTheory.SmGL.jac (stdBlocks ![n, j + 1] hd) π)) χ) :=
    hS.trans (IsSubquotient.of_injective E.toIntertwiningMap E.injective)
  have h2 := isSubquotient_untwist h1 hmul
  obtain ⟨s, hsub, ⟨e0⟩⟩ := GlobalTheory.T.whittaker_two_block_subquotient_tensor k ψ hc ![n, j + 1] _ _ hJs hJf (irrTwist S χ' hχ') h2
  let x : Fin 2 → IrrGL (k := k) := fun a => IrrGL.of (N := ![n, j + 1] a) (s a).ρ (s a).smooth (s a).irr
  have hx0 : x 0 = (IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)) := by
    rw [IrrGL.nu, IrrGL.tw_of]
    exact IrrGL.of_eq_of.2 ⟨e0⟩
  have hjm : jm x hd π ≠ 0 := by
    refine jhMult_ne_zero_iff.2 ?_
    have Ψ : (piTensor fun a => (s a).ρ).Equiv (piTensor fun a => (x a).rep) :=
      piTensorEquiv fun a => IrrGL.equivOf (N := ![n, j + 1] a) (s a).ρ (s a).smooth (s a).irr
    exact (IsSubquotient.of_surjective Ψ.toIntertwiningMap Ψ.surjective).trans hsub
  have key : ∀ (u w : Fin 2 → IrrGL (k := k)), u = w → ∀ hu : ∑ a, (u a).1 = n + j + 1, jm u hu π ≠ 0 →
      ∃ hw : ∑ a, (w a).1 = n + j + 1, 1 ≤ jm w hw π := by
    rintro u _ rfl hu h
    exact ⟨hu, ENat.one_le_iff_ne_zero.2 h⟩
  obtain ⟨hw, hjw⟩ := key x ![(IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2)), x 1]
    (by funext a; fin_cases a; exacts [hx0, rfl]) hd hjm
  exact ⟨x 1, hw, rfl, hjw⟩

theorem cls_arith' (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (u : IrrGL (k := k)) (j : ℕ) :
    dualCl (((dualCl u).nu (j : ℂ)).nu (-(((j : ℂ) + 1) / 2))) = (u.nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
  rw [IrrGL.nu_nu, GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.Zcore.dualCl_dualCl hA, IrrGL.nu_nu]
  congr 1
  ring

end

theorem nuPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
    GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.NuPair k := by
  intro k _ _ _ _ hA N V _ _ ω hs hi hgen
  obtain ⟨ψ, hc, hψ⟩ := exists_continuous_addChar_ne_one k
  have hg : ¬ IsGenericFor ψ ω := fun h => hgen ⟨ψ, hc, hψ, h⟩
  let τ : IrrRep (GL (Fin N) k) := ⟨V, ω, hs, hi⟩
  have hne : Nontrivial V := GlobalTheory.CompanionTheory.BZCuspPair.nontrivial_of_irr τ
  obtain ⟨n, hn0, hnN, hnt2, hlow⟩ := GlobalTheory.CompanionTheory.BZCuspPair.exists_highest ψ hc hψ N ω hs hne hg
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, N = n + 1 + j + 1 := ⟨N - (n + 1) - 1, by omega⟩
  have hc' := GlobalTheory.CompanionTheory.BZCuspPair.continuous_inv_addChar ψ hc
  have hψ' : ψ⁻¹ ≠ 1 := inv_ne_one.2 hψ
  let B : V →ₗ[ℂ] smoothPart ω.dual →ₗ[ℂ] ℂ := LinearMap.flip (smoothPart ω.dual).subtype
  have hBa : ∀ a b, B a b = (b : Module.Dual ℂ V) a := fun _ _ => rfl
  have hB : ∀ g a b, B (ω g a) (contra ω g b) = B a b := by
    intro g a b
    simp only [hBa, contra_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hnd : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0 := fun v hv =>
    GlobalTheory.ContraRefl.exists_smooth_form_ne hs (GlobalTheory.SqIntUnit.compactOpen_basis k _) hv
  obtain ⟨B', hB', hn'⟩ := GlobalTheory.CompanionTheory.BZCuspPair.pair_deriv ψ hc hψ n j ω (contra ω) hs (isSmooth_contra _) B hB hnd
    (GlobalTheory.CompanionTheory.BZCuspPair.phi_vanish ψ hc hψ n j ω hs hlow)
  have hD := GlobalTheory.CompanionTheory.BZCuspPair.deriv_nontrivial ψ n j ω hnt2
  have hci : (contra ω).IsIrreducible := GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA ω hs hi
  obtain ⟨S, f, hf⟩ := deriv_irr_sub ψ hc (n + 1) j ω hs hi hD
  haveI := GlobalTheory.CompanionTheory.BZCuspPair.nontrivial_of_irr S
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : S.V)
  have hw1 : f w₀ ≠ 0 := fun h => hw₀ (hf (by rw [h, map_zero]))
  obtain ⟨w', hw'⟩ := hn' (f w₀) hw1
  obtain ⟨Q, hQ, hQcl⟩ := GlobalTheory.T.pairing_twisted_determinant_subquotient k (n + 1) j _ S (GlobalTheory.BZMir.deriv k ψ⁻¹ j (contra ω))
    (GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ⁻¹ j (isSmooth_contra _)) (B'.comp f.toLinearMap)
    (fun g w v => by
      have := hB' g (f w) v
      simpa [f.isIntertwining] using this)
    (fun h0 => hw' (by simpa using LinearMap.congr_fun (LinearMap.congr_fun h0 w₀) w'))
  have hSq := IsSubquotient.of_injective f hf
  obtain ⟨β, hd, hβ, hjm⟩ := deriv_jm ψ hc (n + 1) j ω hs hi S hSq
  obtain ⟨β₂, hd₂, hβ₂, hjm₂⟩ := deriv_jm ψ⁻¹ hc' (n + 1) j (contra ω) (isSmooth_contra _) hci Q hQ
  obtain ⟨hd₃, hjm₃⟩ := jm_contra hA _ ω hs hi _ _ hd₂ hjm₂
  have hcl : dualCl (((IrrGL.of Q.ρ Q.smooth Q.irr)).nu (-(((j : ℂ) + 1) / 2))) =
      ((IrrGL.of S.ρ S.smooth S.irr).nu (-(((j : ℂ) + 1) / 2))).nu 1 := by
    rw [hQcl]
    exact cls_arith' hA _ j
  have key : ∀ (z w : IrrGL (k := k)), z = w → ∀ hz : ∑ a, (![dualCl β₂, z] a).1 = n + 1 + j + 1,
      1 ≤ jm ![dualCl β₂, z] hz ω →
      ∃ hw : ∑ a, (![dualCl β₂, w] a).1 = n + 1 + j + 1, 1 ≤ jm ![dualCl β₂, w] hw ω := by
    rintro z _ rfl hz h
    exact ⟨hz, h⟩
  obtain ⟨hd₄, hjm₄⟩ := key _ _ hcl hd₃ hjm₃
  have hdeg : (dualCl β₂).1 = β₂.1 := by
    unfold dualCl
    split_ifs <;> rfl
  exact ⟨_, β, dualCl β₂, hd, hd₄, Nat.succ_pos n, by omega, by omega, hjm, hjm₄⟩

end GlobalTheory.CompanionTheory.BZNuPair

end
