module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.UnipUGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.RightOfFd

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.KeyThree
noncomputable section

namespace PositivityTheory.ThKEnd.Cusp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ}

def colOp (i : Fin d) (ρ : Fin d → k) (Y : Matrix (Fin n) (Fin d) k) : Matrix (Fin n) (Fin d) k :=
  Y + Matrix.vecMulVec (fun a => Y a i) ρ

def LeftLaw (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), ∀ γ : GL (Fin n) k,
    l (fun Y => φ (γ.1 * Y)) = ξ (Matrix.GeneralLinearGroup.det γ) * l φ

def ColLaw (ψ : AddChar k ℂ) (S : Set (Fin d)) (i i' : Fin d) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), ∀ ρ : Fin d → k, (∀ s ∈ S, ρ s = 0) → l (fun Y => φ (colOp i ρ Y)) = ψ (ρ i') * l φ


variable (k n d) in
def oneO : Matrix (Fin n) (Fin d) k → ℂ := Set.indicator {Y | ∀ a b, ValuativeRel.valuation k (Y a b) ≤ 1} 1

def torus (i₀ i₁ : Fin d) (x : k) : Matrix (Fin d) (Fin d) k :=
  Matrix.diagonal fun i => if i = i₀ then x else if i = i₁ then x⁻¹ else 1

end Local

def LocSupp : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (i₀ i₁ : Fin d), i₀ ≠ i₁ → ∀ (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ), LeftLaw ξ l → ColLaw ψ {i₀} i₀ i₁ l →
    ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y, ¬ LinearIndependent k ![fun a => Y a i₀, fun a => Y a i₁] → φ Y = 0) → l φ = 0

def LocThree : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ψ : AddChar k ℂ), ψ ≠ 1 →
    ∀ (i₀ i₁ i₂ : Fin d), i₀ ≠ i₁ → i₀ ≠ i₂ → i₁ ≠ i₂ → ∀ (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ), LeftLaw ξ l →
    ColLaw ψ {i₀} i₀ i₁ l → ColLaw ψ {i₀, i₁} i₁ i₂ l → ∀ φ ∈ SB (Matrix (Fin n) (Fin d) k), l φ = 0

def LocTwo : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
    ∀ (ψ : AddChar k ℂ) (c : ℤ), (∀ x, ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) → ψ x = 1) →
    (∃ x, ValuativeRel.valuation k x ≤ ValuativeRel.valuation k ((ϖ ^ (c - 1) : kˣ) : k) ∧ ψ x ≠ 1) →
    ∀ (i₀ i₁ : Fin d), i₀ ≠ i₁ → ∀ (ξ : kˣ →* ℂˣ), (∀ x : kˣ, ValuativeRel.valuation k (x : k) = 1 → ξ x = 1) →
    ∀ l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ, LeftLaw ξ l → ColLaw ψ {i₀} i₀ i₁ l →
    ∀ r : ℂ, r = ξ ϖ * (GlobalTheory.SplitWeil.resCard k : ℂ) ^ ((n : ℤ) - d) → ∃ x : ℂ, ∀ m : ℕ,
      l (fun Y => oneO k n d (Y * torus i₀ i₁ ((ϖ : k) ^ m))) =
        x * ((GlobalTheory.SplitWeil.resCard k : ℂ) * r) ^ (-(m : ℤ)) * ∑ i ∈ Finset.range (2 * m - c + 1).toNat, r ^ i

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def VacBar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) r s r' s', B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ᶠ v : Pl F in cofinite, ∀ (t : E →ₐ[F] Fv F v) ι, M.IsLinBar B.ψ t 1 1 ι → ∃ c : ℂ, ι (M.vac v) = c • oneO (Fv F v) n d

def Places : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    (∀ (v : Pl F) (t : E →ₐ[F] Fv F v), Continuous (piW t)) ∧
    (∀ z : AE F E, ∀ᶠ v : Pl F in cofinite, ∀ t : E →ₐ[F] Fv F v, ValuativeRel.valuation (Fv F v) (piW t z) ≤ 1) ∧
    (∀ (χ : Chr F E) (T : Set (Pl F)), UnrOff χ T → ∀ v ∉ T, ∀ (t : E →ₐ[F] Fv F v) (x : (Fv F v)ˣ),
      ValuativeRel.valuation (Fv F v) (x : Fv F v) = 1 → chrW χ t x = 1) ∧
    {v : Pl F | Nonempty (E →ₐ[F] Fv F v)}.Infinite

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d j : ℕ}


variable (σ) in
structure IsFrame (W : Spc F E d) (u u' : Matrix (Fin d) (Fin j) E) : Prop where
  uu : uᵀ * W.J * u.map σ = 0
  vv : u'ᵀ * W.J * u'.map σ = 0
  uv : uᵀ * W.J * u'.map σ = 1

def colSp (u : Matrix (Fin d) (Fin j) E) : Submodule E (Fin d → E) := Submodule.span E (Set.range uᵀ)


variable (σ) in
def levM (W : Spc F E d) (u u' : Matrix (Fin d) (Fin j) E) (g : GL (Fin j) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E) :=
  1 + incM F u * (g.1 - 1) * incM F (W.J * u'.map σ)ᵀ - incM F u' * (((g⁻¹).1.map (cA σ))ᵀ - 1) * incM F (W.J * u.map σ)ᵀ

def IsLev {W : Spc F E d} (u u' : Matrix (Fin d) (Fin j) E) (m : GL (Fin j) (AE F E) →* UA σ W.J) : Prop :=
  Continuous m ∧ ∀ g, mat (m g) = levM σ W u u' g

def IsChar (σ : E →ₐ[F] E) (χ : AddChar (AE F E) ℂ) : Prop :=
  Continuous χ ∧ ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), ∃ z, At (evFin F v) z ∧ piW (t.comp σ) z = 0 ∧ χ z ≠ 1

structure IsWh (W : Spc F E d) (u : Matrix (Fin d) (Fin j) E) (χ : AddChar (AE F E) ℂ) (Λ : (UA σ W.J → ℂ) → ℂ) : Prop where
  add : ∀ f f', IsAut (W := W) f → IsAut (W := W) f' → Λ (f + f') = Λ f + Λ f'
  smul : ∀ (c : ℂ) f, Λ (c • f) = c * Λ f
  law : ∀ f, IsAut (W := W) f → ∀ (h : UA σ W.J) (g : Matrix (Fin j) (Fin j) (AE F E)), mat h * incM F u = incM F u * g →
    (∀ a b : Fin j, b < a → g a b = 0) → (∀ a, g a a = 1) →
    (∀ z : Fin d → E, (∀ x ∈ colSp u, form σ W.J z x = 0) →
      mat h *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (colSp u : Set (Fin d → E)))) →
    Λ (fun x => f (x * h)) = χ (∑ p : Fin j × Fin j with (p.2 : ℕ) = p.1 + 1, g p.1 p.2) * Λ f

def KeyThree : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (j : ℕ) (u u' : Matrix (Fin (a + a')) (Fin (j + 3)) E),
    IsFrame σ G.W u u' → ∀ χ Λ, IsChar σ χ → IsWh (σ := σ) G.W u χ Λ → ∀ f ∈ ThKEnd.Sig B G om om', ∀ h, Λ (fun x => f (x * h)) = 0

def KeyTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om' →
    ∀ (u u' : Matrix (Fin (a + a')) (Fin 2) E),
    IsFrame σ G.W u u' → ∀ m, IsLev u u' m → ∀ χ Λ, IsChar σ χ → IsWh (σ := σ) G.W u χ Λ → ∀ f ∈ ThKEnd.Sig B G om om', ∀ h₀,
    ∃ V ∈ 𝓝 h₀, ∃ (b : ℕ → GL (Fin 2) (AE F E)) (y : ℕ → ℂ), b 0 = 1 ∧ (∀ i, Matrix.GeneralLinearGroup.det (b i) = 1) ∧
      Tendsto (fun i => ‖y i‖) atTop atTop ∧ ∀ h ∈ V, ∃ x : ℂ, ∀ i, Λ (fun z => f (z * (m (b i) * h))) = x * y i

end PositivityTheory.ThKEnd.Cusp

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.CuspidalAverages.AvgEqOfIsAv
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Cusp

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric GlobalTheory.CuspRep.Generic PositivityTheory.ThKEnd.Two

variable {E : Type} [Field E] [NumberField E] {a : ℕ} {ψ : AddChar (Ad E) ℂ}

structure Pre (ψ : AddChar (Ad E) ℂ) (m : ℕ) (f : GA E a → ℂ) : Prop where
  cont : Continuous f
  left : ∀ γ : GL (Fin a) E, IsMir m γ → ∀ g, f (ratGL E a γ * g) = f g
  law : ∀ k, m < k → ∀ (y : UnipotentBlockColumnIndex a k k → Ad E) (g : GA E a), f (blkU y * g) = ψ (dot (eLast a k) y) * f g

theorem pre_top {f : GA E a → ℂ} (hc : Continuous f) (hl : ∀ γ g, f (ratGL E a γ * g) = f g) : Pre ψ (a - 1) f := by
  refine ⟨hc, fun γ _ => hl γ, fun k hk y g => ?_⟩
  have he : IsEmpty (UnipotentBlockColumnIndex a k k) := ⟨fun t => by have := t.1.2.isLt; have := t.2; omega⟩
  obtain rfl : y = 0 := Subsingleton.elim _ _
  rw [show dot (eLast a k) (0 : UnipotentBlockColumnIndex a k k → Ad E) = 0 by simp [dot], AddChar.map_zero_eq_one, one_mul, blkU, posU_zero, one_mul]

theorem Pre.per (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hf : Pre ψ m f) (g : GA E a) :
    Per (ratV E (UnipotentBlockColumnIndex a m m)) fun x => ψ (-dot (eLast a m) x) * f (blkU x * g) :=
  per_coef hψ _ hf.cont (fun c g' => hf.left _ (isMir_blkU c) g') g

theorem pre_colT (hψ : StdPsi ψ) {m : ℕ} {f : GA E a → ℂ} (hma : m + 1 < a) (hf : Pre ψ (m + 1) f) : Pre ψ m (colT ψ (m + 1) f) := by
  refine ⟨?_, fun γ hγ g => ?_, fun k hk y g => ?_⟩
  · exact GlobalTheory.T.continuous_quotientAverage_periodic_family _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (isCoLat_ratV E _) (GA E a)
      (fun p => ψ (-dot (eLast a (m + 1)) p.2) * f (blkU p.2 * p.1))
      ((hψ.cont.comp ((continuous_dot _).neg.comp continuous_snd)).mul
        (hf.cont.comp (((continuous_posU _).comp continuous_snd).mul continuous_fst))) fun g γ hγ y => (hf.per hψ g).2 γ hγ y
  · rw [colT, GlobalTheory.T.whittakerCoefficient_rationalMirabolic_mul E a ψ hψ m f hf.cont hf.left γ hγ.succ (eLast a (m + 1)) g]
    congr 1
    funext t
    let s0 : UnipotentBlockColumnIndex a (m + 1) (m + 1) := ⟨(⟨m, by omega⟩, ⟨m + 1, hma⟩), Nat.lt_succ_self m, le_refl _, le_refl _⟩
    rw [Finset.sum_eq_single s0 (fun s _ hs => ?_) fun h => absurd (Finset.mem_univ _) h]
    · rw [show eLast (E := E) a (m + 1) s0 = 1 by simp [eLast, s0], one_mul, hγ _ _ (Or.inl (le_refl m))]
      have ht := t.2.1
      simp only [eLast, Matrix.one_apply]
      by_cases h : (t.1.1 : ℕ) = m
      · rw [if_pos (Fin.ext h.symm), if_pos (by omega)]
      · rw [if_neg (fun e => h (congrArg Fin.val e).symm), if_neg (by omega)]
    · rw [eLast, if_neg, zero_mul]
      intro e
      have h2 := s.2.2
      exact hs (Subtype.ext (Prod.ext (Fin.ext (by simp [s0]; omega)) (Fin.ext (by simp [s0]; omega))))
  · rcases Nat.lt_or_ge (m + 1) k with h1 | h1
    · simp only [colT, coefF]
      rw [← avg_const_mul]
      congr 1
      funext x
      rw [← mul_assoc (blkU x), blkU_mul_blkU h1 x y, mul_assoc, hf.law k h1, dot_eLast_shift h1 x y]
      ring
    · obtain rfl : k = m + 1 := by omega
      have hT := GlobalTheory.T.quotientAverage_translate_invariant _ _ (isCoLat_ratV E _) _ (hf.per hψ g) y
      simp only [colT, coefF]
      rw [← hT, ← avg_const_mul]
      congr 1
      funext x
      have hd : dot (eLast a (m + 1)) (x + y) = dot (eLast a (m + 1)) x + dot (eLast a (m + 1)) y := by
        simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hd, show (blkU (x + y) : GA E a) = blkU x * blkU y from posU_add _ x y, ← mul_assoc (ψ _), ← AddChar.map_add_eq_mul,
        mul_assoc (blkU x)]
      congr 2
      abel

theorem whit_pre (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f : GA E a → ℂ}, Pre ψ m f → Pre ψ 0 (whit ψ m f) := by
  induction m with
  | zero => exact fun _ f hf => hf
  | succ m ih => exact fun h f hf => ih (Or.inl (by omega)) (pre_colT hψ (by omega) hf)

theorem whit_add' (hψ : StdPsi ψ) (m : ℕ) : (m < a ∨ m = 0) → ∀ {f f' : GA E a → ℂ}, Pre ψ m f → Pre ψ m f' →
    whit ψ m (fun g => f g + f' g) = fun g => whit ψ m f g + whit ψ m f' g := by
  induction m with
  | zero => exact fun _ f f' _ _ => rfl
  | succ m ih =>
    intro h f f' hf hf'
    have e : colT ψ (m + 1) (fun g => f g + f' g) = fun g => colT ψ (m + 1) f g + colT ψ (m + 1) f' g := funext fun g => by
      simp only [colT, coefF, mul_add]
      exact GlobalTheory.T.quotientAverage_add_of_periodic _ _ (isCoLat_ratV E _) _ _ (hf.per hψ g) (hf'.per hψ g)
    rw [whit_succ, whit_succ, whit_succ, e]
    exact ih (Or.inl (by omega)) (pre_colT hψ (by omega) hf) (pre_colT hψ (by omega) hf')

section Mult

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [T2Space X] {Γ : AddSubgroup X}

instance : LocallyCompactSpace (Multiplicative X) := inferInstanceAs (LocallyCompactSpace X)
instance : SecondCountableTopology (Multiplicative X) := inferInstanceAs (SecondCountableTopology X)
instance : T2Space (Multiplicative X) := inferInstanceAs (T2Space X)

theorem lat_mult (h : IsCoLat Γ) : Lat Γ.toSubgroup := by
  have := h.1
  haveI : SecondCountableTopology Γ := TopologicalSpace.Subtype.secondCountableTopology _
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, a, b⟩ := h.2
  exact ⟨‹Countable Γ›, h.1, K, a, b⟩

theorem avg_eq_of_isAv (h : IsCoLat Γ) [MeasurableSpace (Multiplicative X)] [hB : BorelSpace (Multiplicative X)] {H : Type} [Mul H]
    {ι : Multiplicative X → H} {f c : H → ℂ} (ha : IsAv Γ.toSubgroup ι f c) (x : H)
    (hp : Per Γ fun y => f (ι (Multiplicative.ofAdd y) * x)) : avg Γ (fun y => f (ι (Multiplicative.ofAdd y) * x)) = c x := by
  letI : MeasurableSpace X := ‹MeasurableSpace (Multiplicative X)›
  haveI : BorelSpace X := ⟨hB.1⟩
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := GlobalTheory.T.exists_fundamentalDomain_mass_one_cocompactLattice X Γ h
  have h4 := (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average X Γ h μ 𝓕 h1 h2 _ hp).2.2.2
  rw [h3, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at h4
  rw [← h4]
  exact (ha μ 𝓕
    { map_mul_left_eq_self := h1.map_add_left_eq_self, lt_top_of_isCompact := h1.lt_top_of_isCompact, open_pos := h1.open_pos } ⟨h2.1, h2.2, h2.3⟩ h3 x).symm

end Mult

end PositivityTheory.ThKEnd.Cusp

end
end
