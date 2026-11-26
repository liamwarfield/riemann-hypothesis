module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ISupIndepOfPairwiseOrthogonalDefinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtFoldrLineDer
open scoped TensorProduct NNReal Matrix ContDiff
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.ThK.RealLineGrowthDerivative
open GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

variable {J : Matrix (Fin n) (Fin n) E}

theorem prod_ofFn_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_partial_last {m : ℕ} {H : (Fin (m + 1) → ℝ) → ℂ} (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ fun s : Fin m → ℝ => deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 := by
  let v : Fin (m + 1) → ℝ := Pi.single (Fin.last m) 1
  let L : (Fin m → ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
    ContinuousLinearMap.pi fun i => Fin.lastCases 0 (fun j => ContinuousLinearMap.proj j) i
  have hL : ∀ s t, Fin.snoc (α := fun _ => ℝ) s t = L s + t • v := fun s t => by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [L, v]
    · simp [L, v, Fin.castSucc_ne_last]
  have hd : ∀ s, deriv (fun t => H (Fin.snoc (α := fun _ => ℝ) s t)) 0 = fderiv ℝ H (L s) v := fun s => by
    simp only [hL]
    have h1 : HasDerivAt (fun t : ℝ => L s + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add (L s)
    have h2 := (hH.differentiable (by simp)).differentiableAt (x := L s + (0 : ℝ) • v)
    rw [zero_smul, add_zero] at h2
    have h3 := h2.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    exact h3.deriv
  simp only [hd]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp L.contDiff).clm_apply contDiff_const

theorem contDiff_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∀ (m : ℕ) (δ : Fin m → ℝ → GAd σ J),
      (∀ i, IsRealLine σ J (δ i)) → ∀ x,
      ContDiff ℝ ∞ fun s : Fin m → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => δ i (s i)).prod) := by
  intro l
  induction l with
  | nil => intro _ m δ hδ x; exact hf m δ hδ x
  | cons γ l ih =>
    intro hl m δ hδ x
    have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
    have hH := ih hl' (m + 1) (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ)
      (fun i => Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i) x
    have := contDiff_partial_last hH
    simp only [prod_ofFn_snoc, ← mul_assoc] at this
    simpa only [List.foldr_cons, lineDer] using this

theorem differentiableAt_foldr_lineDer {f : GAd σ J → ℂ} (hf : GlobalTheory.UAut.IsSm σ J f) (l : List (ℝ → GAd σ J))
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (x : GAd σ J) :
    DifferentiableAt ℝ (fun t => l.foldr lineDer f (x * γ t)) 0 := by
  have h := (contDiff_foldr_lineDer hf l hl 1 (fun _ => γ) (fun _ => hγ) x).comp
    (contDiff_pi.2 fun _ => contDiff_id : ContDiff ℝ ∞ fun t : ℝ => fun _ : Fin 1 => t)
  have h' := (h.differentiable (by simp)) 0
  have e : (fun t => l.foldr lineDer f (x * γ t)) = ((fun s : Fin 1 → ℝ => l.foldr lineDer f (x * (List.ofFn fun i => (fun _ => γ) i (s i)).prod)) ∘ fun t : ℝ => fun _ : Fin 1 => t) := by
    funext t; simp
  rw [e]; exact h'

end GlobalTheory.ThK.RealLineGrowthDerivative

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrModelOfIsLin
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.BigNZ

open GlobalTheory.WeilM GlobalTheory.AdelicU

section Generic

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d}

def IsFinPart (M : Model σ X Y) (T : Finset (Pl F)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) ∧ ∀ v, v ∉ T → φ v = M.vac v

def IsLagrModel (M : Model σ X Y) (ψ : AddChar (AF F) ℂ) (v : Pl F) (A A' : Set (Matrix (Fin n) (Fin d) (AE F E)))
    {Z : Type} [TopologicalSpace Z] [Add Z] (co : Matrix (Fin n) (Fin d) (AE F E) → Z)
    (ι : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Z → ℂ)) : Prop :=
  Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB Z : Set _) ∧
  (∀ u ∈ A, ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ z, ι φ₁ z = ι φ (z + co u)) ∧
  ∀ u ∈ A', ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (M.co.rho ψ u) φ φ₁ → ∀ x ∈ A,
    ι φ₁ (co x) = ψ (symp (cA σ) (-1) (incM F X.J) (incM F Y.J) x u) * ι φ (co x)

theorem isFinPart_vac {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} (h : M.IsGood ψ) (T : Finset (Pl F)) : IsFinPart M T M.vac :=
  ⟨fun v => (h.vac v).1, fun _ _ => rfl⟩

theorem isLagrModel_of_isLin {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : Pl F} {π₁ π₀ : AE F E →+* Fv F v} {co ι}
    (h : M.IsLin ψ π₁ π₀ co ι) :
    IsLagrModel M ψ v {u | At (evFin F v) u ∧ u.map π₀ = 0} {u | At (evFin F v) u ∧ u.map π₁ = 0} co ι :=
  ⟨h.bij, fun u hu => h.trans u hu.1 hu.2, fun u hu φ hφ φ₁ hφ₁ a x hx => h.mult u hu.1 hu.2 φ hφ φ₁ hφ₁ a x hx.1 hx.2⟩

end Generic

section Grid

open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num Geo IsTripleOf mulG colV adjV₁)
open GlobalTheory.TripleSpaceW (conjSub)
open GlobalTheory.SkewLat (scLat pairLat)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def IsTied (t : T) (i j : ℕ) (e : Num G i j) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : Geo G i j)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop :=
  Γ.V.L = conjSub (G.Λ (.grid (i + 1) (j + 1))) ∧
  Γ.W.L = pairLat (scLat D.host.AA (G.Λ (.grid i (j + 1)))) (conjSub (scLat D.host.AA (conjSub (G.Λ (.grid (i + 1) j))))) e ∧
  (∀ v, v ∈ X.T ↔ ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) ∧
  ∀ v : Bs.P, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v.1 → splitPrime (Bs.τ v) = w

variable {i j : ℕ}

def mixHalf (e : Num G i j) (ε : AE D) :
    Set (Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :=
  {u | IsHalf ε (mulG (negSp (spW G i j)) (colV e u)ᵀ) ∧ IsHalf ε (adjV₁ e u)}

def mixCo (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) :=
  fromCols (B.coord t w (X := (i, j + 1)) (Y := (i + 1, j + 1)) ⟨i.2.le, j.2⟩ ⟨i.2, j.2⟩
      ((mulG (negSp (spW G i j)) (colV e u)ᵀ).map fun a => cpt w (toEAf D a)))
    (B.coord t w (X := (i + 1, j + 1)) (Y := (i + 1, j)) ⟨i.2, j.2⟩ ⟨i.2, j.2.le⟩ ((adjV₁ e u).map fun a => cpt w (toEAf D a)))ᵀ

def IsLocFn (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : Geo G i j) (w : Pl D.host.E)
    (v : Pl D.host.F) (Ψ : Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w) → ℂ)
    (φ : (Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F v) → ℂ) : Prop :=
  φ ∈ SB _ ∧ ∃ ι, IsLagrModel Γ.M W.ψ v (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι ∧ ι φ = Ψ

end Grid

end GlobalTheory.BigNZ

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslate
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.CongApprox

theorem inc_mem_OhE (D : D7) (x : 𝓞 D.host.E) : inc D (x : D.host.E) ∈ OhE D :=
  Formalism.UG.P.easyc_inclE_mem _ _ _ (RingHom.mem_range.2 ⟨x, rfl⟩)

theorem exists_int_approx (D : D7) (n : ℕ) (hn : 0 < n) (s : AE D) (hs : s ∈ OhE D) :
    ∃ b : 𝓞 D.host.E, ∃ w ∈ OhE D, s = inc D (b : D.host.E) + (n : AE D) * w := by
  rw [← GlobalTheory.AdelicApprox.levelC_natCast]
  obtain ⟨b, t, ht, h⟩ := Formalism.UG.P.csGlob_approx Formalism.UG.P.csGlob_intAdApprox (n : 𝓞 ℚ)
    (Nat.cast_ne_zero.2 hn.ne') s hs
  exact ⟨b, t, ht, h⟩

theorem OhE_le_IhE_top (D : D7) (s : AE D) (hs : s ∈ OhE D) : s ∈ IhE D ⊤ := by
  have h := GlobalTheory.AdelicApprox.absNorm_mul_mem_IhE D ⊤ s hs
  simpa [Ideal.absNorm_top] using h

theorem mul_mem_hatId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (x : AE D) (hx : x ∈ OhE D)
    (t : AE D) (ht : t ∈ hatId D 𝔪) : x * t ∈ hatId D 𝔪 := by
  unfold hatId at ht ⊢
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨b, hb, x * s, mul_mem hx hs, by ring⟩
  | zero => rw [mul_zero]; exact zero_mem _
  | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
  | neg y _ hy => rw [mul_neg]; exact neg_mem hy

theorem exists_mem_approx (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (m : ℕ) (hm : 0 < m) (t : AE D)
    (ht : t ∈ hatId D 𝔪) :
    ∃ b ∈ 𝔪, ∃ y ∈ IhE D ⊤, inc D (b : D.host.E) - t = (m : AE D) * y := by
  unfold hatId at ht
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    obtain ⟨c, w, hw, hsw⟩ := exists_int_approx D m hm s hs
    refine ⟨b * c, Ideal.mul_mem_right c 𝔪 hb, -(inc D (b : D.host.E) * w),
      OhE_le_IhE_top D _ (neg_mem (mul_mem (inc_mem_OhE D b) hw)), ?_⟩
    rw [hsw]
    push_cast
    rw [map_mul]
    ring
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    obtain ⟨b', hb', u', hu', h'⟩ := hy'
    refine ⟨b + b', add_mem hb hb', u + u', add_mem hu hu', ?_⟩
    push_cast
    rw [map_add (f := _)]
    linear_combination h + h'
  | neg y _ hy =>
    obtain ⟨b, hb, u, hu, h⟩ := hy
    refine ⟨-b, neg_mem hb, -u, neg_mem hu, ?_⟩
    push_cast
    rw [map_neg]
    linear_combination -h

end GlobalTheory.CongApprox

namespace GlobalTheory.CongApprox

theorem exists_closeTo_congOne : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  intro D 𝔪 _ a d k hk hcong z _ m hm
  have hinv : CongOne D 𝔪 k⁻¹ := congOne_inv hk hcong
  set K : Matrix (Fin a) (Fin a) (AE D) := (((k⁻¹ : GA D a) : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) with hK
  set T : Matrix (Fin d) (Fin a) (AE D) := z.map (inc D) * (K - 1) with hT
  have hTmem : ∀ i j, T i j ∈ hatId D 𝔪 := by
    intro i j
    rw [hT, Matrix.mul_apply]
    refine sum_mem fun l _ => ?_
    obtain ⟨b, hb⟩ := ‹∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)› i l
    rw [Matrix.map_apply, hb]
    exact mul_mem_hatId D 𝔪 _ (inc_mem_OhE D b) _ (hinv l j)
  choose b hb y hy hby using fun i j => exists_mem_approx D 𝔪 m hm (T i j) (hTmem i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have hKinv : (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D)) = K := by
    rw [hK, Subgroup.coe_inv]
  have e1 : (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) = 1 := by simp
  have hzK : z.map (inc D) * K = z.map (inc D) + T := by
    rw [hT, Matrix.mul_sub, Matrix.mul_one]; abel
  have key : ∀ i j, ((z + Matrix.of fun i j => (b i j : D.host.E)).map (inc D) -
      (((1 : GA D d) : GL (Fin d) (AE D)) : Matrix (Fin d) (Fin d) (AE D)) * z.map (inc D) *
        (((k : GL (Fin a) (AE D))⁻¹ : GL (Fin a) (AE D)) : Matrix (Fin a) (Fin a) (AE D))) i j =
      inc D (b i j : D.host.E) - T i j := by
    intro i j
    rw [e1, Matrix.one_mul, hKinv, hzK, Matrix.map_add _ (map_add (inc D))]
    simp [Matrix.map_apply]
  unfold CloseTo
  exact fun i j => ⟨y i j, hy i j, (key i j).trans (hby i j)⟩

end GlobalTheory.CongApprox
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealMatrixApproxCongruentOneTranslateStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideal_matrix_approx_congruent_one_translate : ∀ (D : D7) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ} (k : GA D a), k ∈ intG D a → CongOne D 𝔪 k → ∀ (z : Matrix (Fin d) (Fin a) D.host.E), (∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)) → ∀ m : ℕ, 0 < m → ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧ CloseTo D ⊤ m (k : GL (Fin a) (AE D)) ((1 : GA D d) : GL (Fin d) (AE D)) z (z + w) := by
  first | exact @GlobalTheory.CongApprox.exists_closeTo_congOne | exact GlobalTheory.CongApprox.exists_closeTo_congOne | (intros; apply GlobalTheory.CongApprox.exists_closeTo_congOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGram
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilSchrodinger

theorem matchPair_cA_eq_sigR (D : D7) (x : AE D) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig x = sigR (AF D.host.F) D.sp.cm.sig x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA, sigR]
  | add x y hx hy => simp_all

theorem matchPair_inv_transpose {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
    (Bm Bi P Q Cm Ci : Matrix n n R) (hBB : Bm * Bi = 1) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hCC : Ci * Cm = 1) (hb : Bmᵀ * P * Cm = P) : Ci * Q * Biᵀ = Q := by
  have e1 : Biᵀ * Bmᵀ = 1 := by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  have e2 : P * Cm = Biᵀ * P := by
    calc P * Cm = (Biᵀ * Bmᵀ) * P * Cm := by rw [e1, Matrix.one_mul]
      _ = Biᵀ * (Bmᵀ * P * Cm) := by simp only [Matrix.mul_assoc]
      _ = Biᵀ * P := by rw [hb]
  have e3 : Cm * Q = Q * Biᵀ := by
    calc Cm * Q = (Q * P) * Cm * Q := by rw [hQP, Matrix.one_mul]
      _ = Q * (P * Cm) * Q := by simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ * (P * Q) := by rw [e2]; simp only [Matrix.mul_assoc]
      _ = Q * Biᵀ := by rw [hPQ, Matrix.mul_one]
  calc Ci * Q * Biᵀ = Ci * (Q * Biᵀ) := Matrix.mul_assoc _ _ _
    _ = Ci * (Cm * Q) := by rw [e3]
    _ = Q := by rw [← Matrix.mul_assoc, hCC, Matrix.one_mul]

theorem matchPair_map_cA (D : D7) {n m : ℕ} (M : Matrix (Fin n) (Fin m) (AE D)) :
    M.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = M.map (sigR (AF D.host.F) D.sp.cm.sig) := by
  ext i j; exact matchPair_cA_eq_sigR D (M i j)

theorem matchPair_memT (D : D7) (T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (hA : JA = T.gramᵀ)
    (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA)) : (a.1 : GL (Fin T.rank) (AE D)) ∈ HR (AF D.host.F) D.sp.cm.sig T.gram := by
  have ha : a.1.1ᵀ * incM D.host.F JA * a.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JA := a.2
  show Formalism.UG.cT _ _ * _ * _ = _
  have := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hA] at this
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA]
  have e : (incM D.host.F T.gramᵀ)ᵀ = incM D.host.F T.gram := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, Matrix.transpose_map]
  rw [e] at this
  exact (Matrix.mul_assoc _ _ _).trans this

theorem matchPair_keeps_inv_gram (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F S.gram⁻¹ := by
  have hb : b.1.1ᵀ * incM D.host.F JB * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = incM D.host.F JB := b.2
  have hxi : IsUnit (incA D D.host.xi0) := (isUnit_iff_ne_zero.2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)).map _
  have hsc : (incM D.host.F (D.host.xi0 • S.gram⁻¹) : Matrix (Fin S.rank) (Fin S.rank) (AE D)) =
      (incA D D.host.xi0 : AE D) • (incM D.host.F S.gram⁻¹ : Matrix (Fin S.rank) (Fin S.rank) (AE D)) := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, incA]
  have t1 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), X * (r • Y) = r • (X * Y) :=
    fun r X Y => Matrix.mul_smul X r Y
  have t2 : ∀ (r : AE D) (X Y : Matrix (Fin S.rank) (Fin S.rank) (AE D)), (r • X) * Y = r • (X * Y) :=
    fun r X Y => Matrix.smul_mul r X Y
  have e1 := congrArg (fun M => ξ • M) hb
  rw [← t2, ← t1, hB, hsc] at e1
  have e2 : b.1.1ᵀ * ((incA D D.host.xi0 : AE D) • incM D.host.F S.gram⁻¹) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) =
      (incA D D.host.xi0 : AE D) • (b.1.1ᵀ * incM D.host.F S.gram⁻¹ * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)) := by
    rw [t1, t2]
  rw [e2] at e1
  exact hxi.smul_left_cancel.1 e1


set_option maxHeartbeats 1000000 in
theorem matchPair_memS (D : D7) (S : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E)
    (hB : ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹)) (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)) :
    ∃ G : GL (Fin S.rank) (AE D), G.1 = (b⁻¹).1.1ᵀ ∧ G ∈ HR (AF D.host.F) D.sp.cm.sig S.gram := by
  have hBB : b.1.1 * (b⁻¹).1.1 = 1 := Units.mul_inv b.1
  have hBB' : (b⁻¹).1.1 * b.1.1 = 1 := Units.inv_mul b.1
  have hdet : IsUnit S.gram.det := (Formalism.L2.Theta.gram_det_ne S).isUnit
  have hPQ : incM D.host.F S.gram⁻¹ * incM D.host.F S.gram = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP : incM D.host.F S.gram * incM D.host.F S.gram⁻¹ = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hCC : (b⁻¹).1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) * b.1.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) = 1 := by
    have := map_mul ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig).toRingHom.mapMatrix :
      Matrix (Fin S.rank) (Fin S.rank) (AE D) →+* Matrix (Fin S.rank) (Fin S.rank) (AE D)) (b⁻¹).1.1 b.1.1
    rw [hBB', map_one] at this
    exact this.symm
  have key := matchPair_inv_transpose _ _ _ _ _ _ hBB hPQ hQP hCC (matchPair_keeps_inv_gram D S JB ξ hB b)
  refine ⟨⟨(b⁻¹).1.1ᵀ, b.1.1ᵀ, by rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩, rfl, ?_⟩
  show Formalism.UG.cT _ _ * _ * _ = _
  unfold Formalism.UG.cT JR
  rw [← matchPair_map_cA, Matrix.transpose_map, Matrix.transpose_transpose]
  exact key

theorem match_pair : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  intro D S T JA JB ξ hA hB a b
  obtain ⟨G, hG, hGm⟩ := matchPair_memS D S JB ξ hB b
  exact ⟨⟨G, hGm⟩, ⟨a.1, matchPair_memT D T JA hA a⟩, rfl, hG⟩

end GlobalTheory.WeilSchrodinger

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPairOfTransposedGramInverseGramStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPair_of_transposedGram_inverseGram : ∀ (D : D7) (S T : HSp D) (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
    ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (a : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA))
      (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB)),
      ∃ (g : GA D S) (h : GA D T), mt T h = a.1.1 ∧ mt S g = (b⁻¹).1.1ᵀ := by
  first | exact @GlobalTheory.WeilSchrodinger.match_pair | exact GlobalTheory.WeilSchrodinger.match_pair | (intros; apply GlobalTheory.WeilSchrodinger.match_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAdd
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict


open GlobalTheory.HolRead in
theorem extWt_arr_eq_wtCol {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (h : HCParam D.R) (p q : ℕ)
    (hpq : p + q = D.R.r) (hr : V.rank = D.R.r) (ρ : D.what₂.Tau)
    (hS : S ρ = Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (c : Fin V.rank) :
    extWt M ρ (arr (nNeg (M.ε ρ)) c) = (wtCol h p q c : ℝ) := by
  have hn : p + q = V.rank := hpq.trans hr.symm
  have hp : p ≤ V.rank := by omega
  have he : IsEnum (Formalism.L2.NTheta.holPar p q (Formalism.L2.NTheta.kapW h p q)) (M.lam ρ) (M.ε ρ) := hS ▸ M.enum ρ
  have hε : ∀ a, M.ε ρ a = decide ((a : ℕ) < p) := fun a => (isEnum_holPar_kapW h hr hn he a).2
  obtain ⟨hn', hx⟩ := GlobalTheory.HolDS.lowK_holPar (Formalism.L2.NTheta.holOK_kapW h p q hpq) he
  have hc := c.2
  by_cases hcq : (c : ℕ) < q
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inr ⟨c, hcq⟩ : Fin p ⊕ Fin q)))
      (by rw [if_pos (by omega)]; simp), hx]
    simp only [wtCol, if_pos hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inr]
  · rw [extWt_arr M ρ hp hε c (Fin.cast hn' (finSumFinEquiv (Sum.inl ⟨c - q, by omega⟩ : Fin p ⊕ Fin q)))
      (by rw [if_neg (by omega)]; simp; omega), hx]
    simp only [wtCol, if_neg hcq, Formalism.L2.NTheta.kapW, Formalism.L2.NTheta.kapQ, Sum.elim_inl]

theorem muVal_castDict {D : D7} {V W : HSp D} (hV : V = W) {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : MuVal V χ mu) :
    MuVal W χ (castDict hV mu) := by
  subst hV
  exact h

theorem extWt_eq_laU_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hM ht i σ hσ hV w hw
  choose e he using fun ρ => (D.hc (lab σ ρ)).e_int i
  refine ⟨fun ρ => -e ρ, ?_, fun k ρ τ hτ a => ?_⟩
  · exact GlobalTheory.HolRead.mu_real_eq_prod_det D R.θ _ _ _ e hM.inf (muVal_castDict hV (ht.laws.muVal _ (inR i) _ hσ))
      fun ρ => he ρ ▸ (ht.chiR i σ hσ).2.2.1 ρ
  · have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
    have hr : (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = D.R.r := by
      have := D.R.m_add_three_le_k
      have hi := i.2
      simp only [Ranks.sigW, Ranks.r]
      omega
    have h1 := extWt_arr_eq_wtCol (R.MW i σ) (D.hc (lab σ ρ)) _ _ (hs ▸ hr :
      ((Wc D i).sig (tauE D ρ)).1 + ((Wc D i).sig (tauE D ρ)).2 = D.R.r) (rank_Wc i) ρ
      (if_pos ((GlobalTheory.ConjReading.branch_of_pins T ht.alg ht.laws.pins σ ρ).1 hσ)) a
    rw [← hw ρ a, hs] at h1
    rw [GlobalTheory.HolRead.SecWt.laU_eq_wtCol D T κ ht.laws ht.alg ht.kap i σ hσ e (fun ρ => (he ρ).symm) k ρ τ hτ,
      Int.cast_injective h1]
    simp

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalWeightEqCharacterExponentAddStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalWeight_eq_character_exponent_add : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.IsModels → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → ∃ e : D.what₂.Tau → ℤ, (∀ u ∈ GinfC (Wc D i), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) u = ∏ ρ, (archM (Wc D i) (R.θ ρ) u).det ^ e ρ) ∧ ∀ k ρ (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ a : Fin (Wc D i).rank, w ρ a = (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) k τ (Fin.cast (rank_Wc i) a) + e ρ := by
  first | exact @GlobalTheory.HolDict.extWt_eq_laU_add | exact GlobalTheory.HolDict.extWt_eq_laU_add | (intros; apply GlobalTheory.HolDict.extWt_eq_laU_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharEqOneOnPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharEqOneOnPrincipalLevel
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.PrincLevChar

theorem castDict_apply {D : D7} {Y : Type} {V W : HSp D} (hV : V = W) (μ : GA D V → Y) (k : GA D W) :
    castDict hV μ k = μ (cast (congrArg (GA D) hV.symm) k) := by
  subst hV
  rfl


set_option maxHeartbeats 1000000 in
theorem char_eq_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM ht hpb i σ hσ hV k hk
  rw [castDict_apply]
  exact GlobalTheory.T.dictionary_character_trivial_on_principal_level T R κ v₀ hL ht hpb i (res T σ) hσ hV _
    (((GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM ht hpb i σ hσ hV).1 k).1 hk)

end GlobalTheory.HolDict.PrincLevChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryCharEqOneOnPrincipalLevelStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ k ∈ (levG (Wc D i) (R.βW i) (R.datWp i R.triv)), castDict hV (T.mu ((i : ℕ) + 1) (res T σ)) k = 1 := by
  first | exact @GlobalTheory.HolDict.PrincLevChar.char_eq_one | exact GlobalTheory.HolDict.PrincLevChar.char_eq_one | (intros; apply GlobalTheory.HolDict.PrincLevChar.char_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbedding
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem castDict_laws {D : D7} {V W : HSp D} (hV : V = W) {r : ℕ} (hr : W.rank = r) {Comp : Type}
    (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r)
    (mu : GA D V → ℂ) (Kf : Subgroup (GA D V)) (Kf' : Subgroup (GA D W))
    (hK : ∀ g : GA D W, g ∈ Kf' ↔ cast (congrArg (GA D) hV.symm) g ∈ Kf)
    (hu : ∃ th hr', (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr')
    (hm : ∃ hr' : V.rank = r, ∀ k, ModelW V hr' (X k)) (hmu : MuUnit V dict mu) (hc : Continuous mu) :
    (∃ th, (∀ k τ, IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif W (castDict hV dict) Kf' th hr) ∧
      (∀ k, ModelW W hr (X k)) ∧ MuUnit W (castDict hV dict) (castDict hV mu) ∧ Continuous (castDict hV mu) := by
  subst hV
  obtain rfl : Kf' = Kf := Subgroup.ext hK
  obtain ⟨th, hr', h1, h2⟩ := hu
  obtain ⟨hr'', h3⟩ := hm
  exact ⟨⟨th, h1, h2⟩, h3, hmu, hc⟩

theorem goodDict_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ hL hM h hpb i σ hσ hV w hw
  obtain ⟨hK, -, hfin, hopen⟩ := GlobalTheory.T.realisation_principalLevel_eq_coreLevel_open D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  obtain ⟨h1, h2, h3, h4⟩ := castDict_laws hV (rank_Wc i) _ _ (T.mu ((i : ℕ) + 1) (res T σ)) _ _ hK
    (h.laws.dictU _ hj _ hσ) (h.laws.modelW _ hj _ hσ) (h.laws.muUnit _ hj _ hσ) (h.laws.muCont _ hj _ hσ)
  have hc : ∀ k, ‖T.cE ((i : ℕ) + 1) (res T σ) k‖ = 1 := h.laws.cUnit _ hj _ hσ
  exact
    { inf := hM.inf
      base := GlobalTheory.T.base_frame_of_realization_models D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV
      unif := h1
      model := h2
      muUnit := h3
      muCont := h4
      chi := h.laws.chiTriv _ hj _ hσ _ _ (dom_wtA (κ i))
      cNe := fun k h0 => by
        have := hc k
        rw [h0, norm_zero] at this
        exact zero_ne_one this
      cBdd := ⟨1, fun k => (hc k).le⟩
      fin := @Finite.of_fintype _ (T.U ((i : ℕ) + 1) (res T σ)).fin
      levFin := hfin
      levOpen := hopen
      muK := GlobalTheory.T.dictionaryChar_eq_one_on_principalLevel D G Pl0 T0 A T R κ v₀ hL hM h hpb i σ hσ hV
      wt := GlobalTheory.T.extremalWeight_eq_character_exponent_add D G Pl0 T0 A T R κ v₀ hM h i σ hσ hV w hw }

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreDictionaryGoodAtGoodEmbeddingStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coreDictionary_good_at_good_embedding : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.toLevCh.Is A.μ0 → R.IsModels → TieIn T R κ v₀ → T.pb = R.C.P.pb → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i, ∀ w, WtIs (R.MW i σ) w → GoodDict R.θ (R.MW i σ) w (rank_Wc i) (T.U ((i : ℕ) + 1) (res T σ)).X (laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n) (castDict hV (T.dict ((i : ℕ) + 1) (res T σ))) (castDict hV (T.mu ((i : ℕ) + 1) (res T σ))) (T.cE ((i : ℕ) + 1) (res T σ)) (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) := by
  first | exact @GlobalTheory.HolDict.goodDict_core | exact GlobalTheory.HolDict.goodDict_core | (intros; apply GlobalTheory.HolDict.goodDict_core <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder ENNReal
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def reDens (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem loc_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α - β) i v = A.loc α i v - A.loc β i v := by
  unfold loc; split_ifs
  · rfl
  · exact (sub_zero 0).symm

theorem dens_sub' (x y : Alt n) : dens (x - y) = dens x - dens y := by
  simp only [dens, map_sub, Finsupp.sub_apply, sub_div]

theorem reDens_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.reDens (α - β) i v = A.reDens α i v - A.reDens β i v := by
  simp only [reDens, loc_sub, dens_sub', Complex.sub_re]

theorem reDens_compat {α : A.Fld} (hα : A.IsForm α) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    A.reDens α i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * A.reDens α j (A.e j y) := by
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [reDens]
  erw [h1, h2, h3, GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul]
  rw [Complex.re_ofReal_mul]
  rfl

theorem continuousOn_reDens {α : A.Fld} (hα : A.IsForm α) (i : A.ι) :
    ContinuousOn (A.reDens α i) (A.e i).target := by
  have := (hα.smooth i Finset.univ).continuousOn
  exact Complex.continuous_re.comp_continuousOn (this.div_const _)

theorem aemeasurable_ofReal_chart [MeasurableSpace M] (e : OpenPartialHomeomorph M (V n)) (r : V n → ℝ)
    (hr : ContinuousOn r e.target) :
    AEMeasurable (fun v => ENNReal.ofReal (r (e (e.symm v)))) (volume.restrict (e.target ∩ e.symm ⁻¹' univ)) := by
  rw [preimage_univ, inter_univ]
  have h := (ENNReal.continuous_ofReal.comp_continuousOn hr).aemeasurable (μ := volume) e.open_target.measurableSet
  refine h.congr ((ae_restrict_iff' e.open_target.measurableSet).2 (Filter.Eventually.of_forall fun v hv => ?_))
  simp [e.right_inv hv]

theorem ofReal_compat (r : A.ι → V n → ℝ)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source) (hj : y ∈ (A.e j).source) :
    ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]

theorem glueMeas_add_three [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (r₁ r₂ r₃ : A.ι → V n → ℝ)
    (hr₁ : ∀ i, ContinuousOn (r₁ i) (A.e i).target) (hr₂ : ∀ i, ContinuousOn (r₂ i) (A.e i).target)
    (hc₁ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₁ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₁ j (A.e j y))
    (hc₂ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₂ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₂ j (A.e j y))
    (hc₃ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₃ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₃ j (A.e j y)) :
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) univ =
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₂ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₃ i (A.e i y))) univ := by
  have c₁ := A.ofReal_compat r₁ hc₁
  have c₂ := A.ofReal_compat r₂ hc₂
  have c₃ := A.ofReal_compat r₃ hc₃
  rw [ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aemeasurable_ofReal_chart (A.e i) _ (hr₁ i)).add (aemeasurable_ofReal_chart (A.e i) _ (hr₂ i))),
    ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aemeasurable_ofReal_chart (A.e i) _ (hr₁ i))]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal (-x) + ENNReal.ofReal y =
      ENNReal.ofReal (-(x - y)) + ENNReal.ofReal x + ENNReal.ofReal (-y) := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x - y) 0 + max (-x) 0 + max y 0 = max (-(x - y)) 0 + max x 0 + max (-y) 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x - y), m (-x), m y, m (-(x - y)), m x, m (-y),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

theorem integral_sub [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α - β) = A.integral α - A.integral β := by
  have hF := A.reDens_compat hα
  have hG := A.reDens_compat hβ
  have cF := A.continuousOn_reDens hα
  have cG := A.continuousOn_reDens hβ

  let lin (c d : ℝ) : A.ι → V n → ℝ := fun i v => c * A.reDens α i v + d * A.reDens β i v
  have hlin (c d : ℝ) : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      lin c d i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * lin c d j (A.e j y) := by
    intro i j y hi hj
    simp only [lin, hF i j y hi hj, hG i j y hi hj]
    ring
  have clin (c d : ℝ) (i : A.ι) : ContinuousOn (lin c d i) (A.e i).target :=
    (continuousOn_const.mul (cF i)).add (continuousOn_const.mul (cG i))
  let P (c d : ℝ) : ℝ≥0∞ := ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (lin c d i (A.e i y))) univ
  have fin (c d : ℝ) : P c d ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (lin c d) (clin c d) (hlin c d)
  have part_eq (γ : A.Fld) (ε : ℤˣ) (c d : ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = lin c d i v) :
      A.part γ ε univ = P c d := by
    simp only [part, P]
    congr 2
    funext i y
    rw [← h]
    rfl
  have e1 := part_eq (α - β) 1 1 (-1) fun i v => by simp [lin, reDens_sub]; ring
  have e2 := part_eq (α - β) (-1) (-1) 1 fun i v => by simp [lin, reDens_sub]; ring
  have e3 := part_eq α 1 1 0 fun i v => by simp [lin]
  have e4 := part_eq α (-1) (-1) 0 fun i v => by simp [lin]
  have e5 := part_eq β 1 0 1 fun i v => by simp [lin]
  have e6 := part_eq β (-1) 0 (-1) fun i v => by simp [lin]
  have key : P 1 (-1) + P (-1) 0 + P 0 1 = P (-1) 1 + P 1 0 + P 0 (-1) := by
    simp only [P]
    rw [← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _),
      ← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _)]
    congr 2
    funext i y
    have := ofReal_posNeg (A.reDens α i (A.e i y)) (A.reDens β i (A.e i y))
    simp only [lin]
    convert this using 3 <;> ring_nf
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)] at key'
  simp only [integral, Measure.real, e1, e2, e3, e4, e5, e6]
  linarith

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_sub_of_isForm : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.integral (α - β) = A.integral α - A.integral β :=
  fun A α β hα hβ => A.integral_sub α β hα hβ

end GlobalTheory.CxForm.HolAtlas
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpace
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.SkewGram

theorem det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (X : Spc F E n) (r s : ℕ), X.IsSkew σ B r s → X.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B n X r s h hJ
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨hrs, A, hA⟩ := h.sig w
  have hM : (Complex.I • X.J.map (B.emb w).1).det = 0 := by
    rw [Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hJ, map_zero, mul_zero]
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hrs)
  let P : Matrix (Fin n) (Fin n) ℂ := A.submatrix id e.symm
  have key : Pᵀ * (Complex.I • X.J.map (B.emb w).1) * P.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)).submatrix e.symm e.symm := by
    rw [← hA]; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_mul, Matrix.det_mul, hM] at hd
  rw [Matrix.det_neg, Matrix.det_one, Matrix.det_one, mul_one, one_mul, mul_zero, zero_mul] at hd
  exact (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) hd.symm

end GlobalTheory.SkewGram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.VmTwo

theorem twoSided_goodInert : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hL hW hE hS P hG hc
  have hcore := (GlobalTheory.CoreOfWeak.core_of_weak R F hW hE).1
  exact GlobalTheory.T.twoSidedHeckePartner_inertPrime hH R.toRealDat F.lv2 hL hcore hS _ P hG hc (GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place R F hW hE _ P hG hc)

end GlobalTheory.VmTwo
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLiftStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_partner_combination_good_inert_lift : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) := by
  first | exact @GlobalTheory.VmTwo.twoSided_goodInert | exact GlobalTheory.VmTwo.twoSided_goodInert | (intros; apply GlobalTheory.VmTwo.twoSided_goodInert <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass

namespace GlobalTheory.RatUDiscreteSub

theorem discreteTopology_subgroupOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)),
    DiscreteTopology ((ratU σ J).subgroupOf N) := by
  intro F E _ _ _ _ _ σ n J N
  haveI := GlobalTheory.RatUDiscrete.discreteTopology_ratU F E σ n J
  let φ : (ratU σ J).subgroupOf N → ratU σ J := fun x => ⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩
  have h2 : Topology.IsEmbedding (fun x : (ratU σ J).subgroupOf N => ((x : N) : UA σ J)) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hφ : Topology.IsEmbedding φ :=
    (Topology.IsEmbedding.of_comp_iff (Topology.IsEmbedding.subtypeVal (p := fun x : UA σ J => x ∈ ratU σ J))).1 h2
  exact hφ.discreteTopology

end GlobalTheory.RatUDiscreteSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteRationalPointsSubgroupStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_rational_points_subgroup : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (N : Subgroup (UA σ J)), DiscreteTopology ((ratU σ J).subgroupOf N) := by
  first | exact @GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | exact GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf | (intros; apply GlobalTheory.RatUDiscreteSub.discreteTopology_subgroupOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineMemInfPoints
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RealLineInf

theorem realLine_mem_infPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (β : ℝ → GAd σ J), IsRealLine σ J β → ∀ t, β t ∈ infPts σ J := by
  intro F E _ _ _ _ _ σ n J β hβ t
  obtain ⟨w, τ, Z, -, h⟩ := hβ
  obtain ⟨y, hy, -⟩ := h t
  rw [hy]
  exact mem_infPts.2 (projFin_embArch σ J w y)

end GlobalTheory.RealLineInf
end
