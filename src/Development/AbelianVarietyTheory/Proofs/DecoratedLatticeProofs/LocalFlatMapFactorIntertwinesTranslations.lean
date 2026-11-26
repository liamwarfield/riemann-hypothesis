module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsPreserveSchwartzBruhatAndSurjective
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageRealDataConjValueMemCuspForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatSchwartzLinear

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslations
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatTrans

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem ι_sandwich (a c : AE D) (m : k) : p.ι (p.π a * m * p.π c) = a * p.ι m * c := by
  rw [GlobalTheory.LocChar.ι_mul, GlobalTheory.LocChar.ι_mul, p.ι_π, p.ι_π]
  have h := GlobalTheory.LocChar.e_mul_ι p m
  linear_combination (a * c * p.e + a * c) * h

theorem mul_map_ι_mul {a b l m : Type} [Fintype a] [Fintype b] (A : Matrix m a (AE D)) (M : Matrix a b k)
    (C : Matrix b l (AE D)) : A * M.map p.ι * C = (A.map p.π * M * C.map p.π).map p.ι := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, Matrix.map_apply, Finset.sum_mul, map_sum, ι_sandwich]

theorem map_incA_map {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) : (M.map (incA D)).map p.π = M.map p.pr := by
  ext; rfl

theorem ι_mem_idAt : ∃ v, ∀ y : k, p.ι y ∈ GlobalTheory.FinPl.idAt D (· = v) := by
  obtain ⟨-, he, v, ε, hε, hsum⟩ := p.split
  refine ⟨v, fun y => GlobalTheory.FinPl.Model.mem_idAt_iff.2 ?_⟩
  have hε' := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hε
  subst hε'
  rw [← hsum]
  have h1 := GlobalTheory.LocChar.e_mul_ι p y
  have h2 : cA D p.e * p.e = 0 := by rw [mul_comm]; exact he
  linear_combination (1 - cA D p.e) * h1 + p.ι y * h2

theorem sb_translate {X : Type} [TopologicalSpace X] [AddGroup X] [IsTopologicalAddGroup X] {Φ : X → ℂ}
    (hΦ : Φ ∈ SB X) (t : X) : (fun z => Φ (z + t)) ∈ SB X :=
  ⟨hΦ.1.comp_continuous (continuous_add_const t), hΦ.2.comp_homeomorph (Homeomorph.addRight t)⟩

section Local
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

def bigPt (c ρ : ℕ) (x : Matrix n (n' ⊕ Unit) k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks x.toCols₁ (Matrix.of fun r i => if i.val = ρ then x r (Sum.inr ()) else 0) 0 0

theorem flCol_translate [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (c ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x t : Matrix n (n' ⊕ Unit) k) :
    GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (fun z => Φ (z + bigPt c ρ x)) t = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ (t + x) := by
  unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
  congr 1
  funext e
  have h1 : affPt (ρ + 1) t.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => t r (Sum.inr ())) + bigPt c ρ x =
      affPt (ρ + 1) (t + x).toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) (fun r => (t + x) r (Sum.inr ())) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, add_right_comm]
    · by_cases h : j.val = ρ <;> simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt, h, add_assoc]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
    · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, bigPt]
  have h2 : ch (affPt (ρ + 1) t.toCols₁ e) = ch (affPt (ρ + 1) (t + x).toCols₁ e) := by
    simp [ch, affPt, basePt]
  simp only [h1, h2]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [DecidableEq n] [DecidableEq n'] in
theorem mul_bigPt_mul {a b : Type} {c ρ : ℕ} (j₀ : Fin (c + 1)) (hj : j₀.val = ρ) (β : Matrix a (n ⊕ Fin c) k) (β₀ : Matrix a n k)
    (γ : Matrix (n' ⊕ Fin (c + 1)) b k) (γ₀ : Matrix (n' ⊕ Unit) b k) (hβ : ∀ r i, β r (Sum.inl i) = β₀ r i)
    (hγ : ∀ i s, γ (Sum.inl i) s = γ₀ (Sum.inl i) s) (hγ' : ∀ s, γ (Sum.inr j₀) s = γ₀ (Sum.inr ()) s)
    (x : Matrix n (n' ⊕ Unit) k) : β * bigPt c ρ x * γ = β₀ * x * γ₀ := by
  ext r s
  have hj' : ∀ j : Fin (c + 1), j.val = ρ ↔ j = j₀ := fun j => by rw [← hj, Fin.val_inj]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, bigPt, hβ, hγ, hj', hγ', Finset.sum_ite_irrel]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem rows_of_inverse {N N₀ c : ℕ} (j₀ : Fin (c + 1)) (F : Frame k N (n' ⊕ Fin (c + 1))) (F₀ : Frame k N₀ (n' ⊕ Unit))
    (q : Matrix (Fin N₀) (Fin N) k) (h1 : ∀ r i, (q * F.β) r (Sum.inl i) = F₀.β r (Sum.inl i))
    (h2 : ∀ r, (q * F.β) r (Sum.inr j₀) = F₀.β r (Sum.inr ())) (h3 : ∀ r j, j ≠ j₀ → (q * F.β) r (Sum.inr j) = 0) :
    (∀ i s, F.γ (Sum.inl i) s = (F₀.γ * q) (Sum.inl i) s) ∧ ∀ s, F.γ (Sum.inr j₀) s = (F₀.γ * q) (Sum.inr ()) s := by
  let σ : n' ⊕ Unit → n' ⊕ Fin (c + 1) := Sum.map id fun _ => j₀
  have hq : F₀.β * F.γ.submatrix σ id = q := by
    conv_rhs => rw [← Matrix.mul_one q, ← F.βγ, ← Matrix.mul_assoc]
    ext r s
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
      Finset.sum_eq_single j₀ (fun j _ hj => by rw [h3 r j hj, zero_mul]) (by simp), h2]
    simp [h1, σ]
  have hγ : F₀.γ * q = F.γ.submatrix σ id := by rw [← hq, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul]
  rw [hγ]
  exact ⟨fun _ _ => rfl, fun _ => rfl⟩

end Local

theorem proj_laws {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) :
    d.p0.map p.π * d.i₀.map p.pr = 1 ∧ d.p0.map p.π * d.e.map p.pr = 0 ∧ d.p0.map p.π * d.e'.map p.pr = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_j0).trans (Matrix.map_one _ (map_zero _) (map_one _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jX).trans (Matrix.map_zero _ (map_zero _))
  · rw [← map_incA_map, ← Matrix.map_mul]
    exact (congrArg (·.map p.π) d.p0_jY).trans (Matrix.map_zero _ (map_zero _))

def prHom : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prHom p := rfl

theorem up_bigPt {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (hC : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV) (hJ : p.IsJacFrame J s hh G₀ FW)
    (x : Matrix n (n' ⊕ Unit) k) :
    p.up FV FW (bigPt c ρ x) = B.d.ext0 J.W (J.d.inc0 B.V₀ (p.up F₀ G₀ x)) := by
  obtain ⟨hc, hinl, hlt, heq, hgt⟩ := hB
  obtain ⟨q1, q2, q3⟩ := proj_laws p B.d
  let j₀ : Fin (c + 1) := ⟨ρ, by omega⟩
  have col : ∀ (r : Fin B.V₀.rank) (j : n' ⊕ Fin (c + 1)) (a : k) (y : Fin B.V.rank → k), (∀ r', FV.β r' j = a * y r') →
      (B.d.p0.map p.π * FV.β) r j = a * (B.d.p0.map p.π *ᵥ y) r := fun r j a y h => by
    simp only [Matrix.mul_apply, h, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_left_comm]
  obtain ⟨g1, g2⟩ := rows_of_inverse j₀ FV F₀ (B.d.p0.map p.π)
    (fun r i => by
      rw [hC.1, ← Matrix.one_mul (B.o.iA.map p.pr * FA.β), ← q1, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [hinl, pr_eq, Matrix.map_mul, Matrix.mul_assoc])
    (fun r => by
      rw [col r _ s (B.d.i₀.map p.pr *ᵥ fun i => p.pr (vecB B.o B.ζ i)) fun r' => by
        rw [heq j₀ rfl, pr_eq, RingHom.map_mulVec]; rfl, Matrix.mulVec_mulVec, q1, Matrix.one_mulVec, hC.2])
    (fun r j hj => by
      have hj' : j.val ≠ ρ := fun h => hj (Fin.ext h)
      rcases lt_or_gt_of_ne hj' with h | h
      · rw [col r _ _ _ (hlt ⟨j.val, h⟩ j rfl)]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q2 r) ⟨j.val, h⟩)
      · have := j.2
        rw [col r _ _ _ (hgt ⟨2 * ρ - j.val, by omega⟩ j (by simp only; omega))]
        exact mul_eq_zero_of_right _ (congrFun (congrFun q3 r) ⟨2 * ρ - j.val, by omega⟩))
  rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Place.up, Place.up,
    mul_bigPt_mul j₀ rfl FW.β _ FV.γ _ hJ.2.1 g1 g2, ← map_incA_map]
  refine Eq.trans ?_ (mul_map_ι_mul p J.d.j0 _ B.d.p0).symm
  simp only [Matrix.mul_assoc]
  rfl

theorem factor_trans : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (x : Matrix n (n' ⊕ Unit) k) (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = Ψ.1 (t + x)) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ (p.up F₀ G₀ x) (L₀ Ψ) := by
  intro D _ hFLs _ k _ _ _ _ _ _ p ν hν ψ ψk hpc ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW hC hB hJ Tm hTm L₀ hL₀ x Ψ Ψ' hΨ
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hpc).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦ, hΦΨ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have h1 : flatBF st (Tm ⟨Φ, hΦ⟩) = L₀ Ψ := hL₀ _ _ hΦΨ.symm
  have h2 : flatBF st (Tm ⟨_, sb_translate hΦ (bigPt c ρ x)⟩) = L₀ Ψ' := hL₀ _ _ (by
    funext t
    rw [hΨ, ← hΦΨ]
    exact (flCol_translate ψk ν c ρ Φ x t).symm)
  have h3 := hTm.trans (bigPt c ρ x) ⟨Φ, hΦ⟩ ⟨_, sb_translate hΦ (bigPt c ρ x)⟩ fun _ => rfl
  obtain ⟨v, hv⟩ := ι_mem_idAt p
  rw [← h2, h3, up_bigPt p B J s _ FA F₀ FV G₀ FW hC hB hJ, ← h1]
  exact ((hFLs ψ (· = v)).1 ρ B J st).Heisenberg₂.core _ (hTm.theta _) _ fun i j => hv _

end GlobalTheory.FlatTrans
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesTranslationsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMap_factor_intertwines_translations : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (x : Matrix n (n' ⊕ Unit) k) (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = Ψ.1 (t + x)) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ (p.up F₀ G₀ x) (L₀ Ψ) := by
  first | exact @GlobalTheory.FlatTrans.factor_trans | exact GlobalTheory.FlatTrans.factor_trans | (intros; apply GlobalTheory.FlatTrans.factor_trans <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.ExactNS

variable {D : D7}

theorem petersson_conj (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (X : Set (GA D V))
    (hX : IsFundamentalDomain (GQ V) X ν)
    (f g : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) (hg : ∀ γ ∈ GQ V, ∀ h, g (γ * h) = g h) :
    GlobalTheory.Cusp.petersson V ν (fun h => conj (f h)) (fun h => conj (g h)) = conj (Lift.pet ν X f g) := by
  haveI := hν
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun h => conj (f h) * conj (conj (g h))) := fun γ hγ h => by
    simp only [hf γ hγ, hg γ hγ]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => conj (f h) * conj (conj (g h))) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  unfold Lift.pet
  rw [← integral_conj]
  simp only [map_mul]

theorem up_conj {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (hν : s.ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ s.V) s.fd s.ν) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (hF : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g) :
    GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = fun h => conj (p.up φ F h) := by
  haveI := hν
  funext h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθl : ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g)) := fun γ hγ x => by
    simp only [hθl γ hγ, hF γ hγ]
  simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ s.V) _ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ s.V) s.ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]

theorem up_leftInv {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : ∀ γ ∈ GQ s'.V, ∀ h, p.up φ F (γ * h) = p.up φ F h := by
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθr : ∀ g, ∀ γ ∈ GQ s'.V, ∀ h, thetaKO p.ω g (γ * h) (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro g γ hγ h
    have e : ((g, γ * h) : GA D s.V × GA D s'.V) = (1, γ) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut 1 (one_mem _) γ hγ _ (hp.weil.om_pres _ _ hΦ)
  intro γ hγ h
  simp only [Step.up, hθr _ γ hγ]

theorem stepExactNS : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  intro D hHF hSoft hPeel hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC u₁ u₂ B hB hQ hNS l hl
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsF⟩ := id hs
  obtain ⟨hr', -, hs'F⟩ := id hs'
  have hv : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hRC.1, rfl⟩
  by_cases h0 : PiTensorProduct.tprod ℂ v = 0
  · have hz : ∀ g, zReal p m X φ v g = 0 := by
      intro g
      have hp0 := hMet.pure v v
      simp only [h0, map_zero, LinearMap.zero_apply] at hp0
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 hp0.symm
      have h0τ : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := inner_self_eq_zero.1 hτ
      simp only [zReal]
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0τ, inner_zero_left])]
      simp
    simp [h0, hz, Step.up, Lift.pet]
  have hF₁ : PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) ≠ 0 := fun h =>
    hB.1 ((hSoft c w hw k hk.le s hs).2.2.1 u₁ _ h0 h)
  have hparF : ParFun c s (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) B := hB.2 _ hF₁
  have hFlat := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw k hk.le s hs hr
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le _ hsF
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk _ hs'F
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split D c (k + 1) _ hk hs'F
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hgap c w hw k hk s s' hs hs' p hp
  set F₁ := PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) with hF₁def
  set F₂ := PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v) with hF₂def
  have hu1 : (fun g => conj (F₁ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₁.1, hFlat u₁.2⟩ _ hv
  have hu2 : (fun g => conj (F₂ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₂.1, hFlat u₂.2⟩ _ hv
  have hrk0 : s.V.rank = D.R.rankY k := hsF.rank
  have hrk1 : s'.V.rank = D.R.rankY (k + 1) := hs'F.rank
  have hr1 : 1 ≤ s.V.rank := by
    rw [hrk0]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht2 : 2 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hrk1, hrk0]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      m X :=
    { setting := ⟨hr1, by omega, hrk, hc.inf, hsF.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hsF.selfDual, hs'F.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2.1, (hfock φ).2.1⟩
  have hsph : GlobalTheory.Core.Rk.IP.SphFun s.V s.Λ c.S (fun g => conj (F₂ g)) := by
    obtain ⟨-, hoffS, -⟩ := GlobalTheory.ChainOnto.LevelFacts.levFacts D c hc k hk.le _ hsF
    have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 (hFlat u₂.2))
    intro v' hv' κ hκ g
    obtain ⟨hκL, hκχ⟩ := hoffS v' hv' κ hκ
    have e : F₂ = PiTensorProduct.lift.symm (u₂ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    simp only [e]
    have hlev := hT.lev v _ hκL g
    rw [hκχ, one_mul] at hlev
    exact congrArg (starRingEnd ℂ) hlev
  have hIM : IsMajOf c s a := ⟨hmaj, hmaj_eq⟩
  obtain ⟨s₁, hs₁, hLI⟩ := hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC a hIM
  obtain ⟨hLint, hLeq⟩ := hLI u₁ u₂
  have hint : ∃ z : ℝ, z < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) z) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    refine ⟨max s₁ ((D.R.t : ℝ) / 2 - 1 / 2), max_lt hs₁ (by linarith), ?_⟩
    exact (hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv _
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (hLint _ (le_max_left _ _))).1
  have hPt := hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv ((D.R.t : ℝ) / 2)
    (by linarith) (hLint _ hs₁.le)
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    m X hPair ht2 (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hsF.haar hs'F.haar
    _ hu1 _ hu2 B hparF hsph hNS hint
  have key := hval l hl
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hI : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g ∂s.ν =
      locQ c w k * ((∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)) := by
    rw [← hLeq, ← hPt.2 rfl]
    change _ = ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, flatInt p m X a φ F₁ F₂ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν
    congr 1
    funext g
    rw [← hsZ]
    exact (GlobalTheory.Core.Rk.IP.integrand_sZero (A := s.V) (B := s'.V) p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) _ _ g).symm
  have hFl : ∀ F : GA D s.V → ℂ, (fun g => conj (F g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA →
      ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun F hF γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hF.1.1.left γ hγ g)
  rw [ExactNS.up_conj p hp hsF.haar hsF.fund φ F₁ (hFl F₁ hu1), ExactNS.up_conj p hp hsF.haar hsF.fund φ F₂ (hFl F₂ hu2),
    ExactNS.petersson_conj s'.V s'.ν hs'F.haar s'.fd hs'F.fund _ _ (ExactNS.up_leftInv p hp φ F₁)
      (ExactNS.up_leftInv p hp φ F₂), hI] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [Complex.conj_conj] at key'
  change Lift.pet s'.ν s'.fd _ _ = _
  rw [key']
  simp only [dS, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.ChainTw.ExactNS

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftChainStep_exact_innerProduct : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  first | exact @GlobalTheory.ChainTw.ExactNS.stepExactNS | exact GlobalTheory.ChainTw.ExactNS.stepExactNS | (intros; apply GlobalTheory.ChainTw.ExactNS.stepExactNS <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplication
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplication
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

noncomputable section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FlatBFLoc.ModelModul
variable {D : D7}

theorem symplectic_pairing_ext_zero_inc_zero {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (t : WO V W)
    (y : WO V₀ W₀) : symplO V W t (dV.ext0 W (dW.inc0 V₀ y)) = symplO V₀ W₀ (dW.p0 ⬝ t ⬝ dV.j0) y := by
  unfold symplO
  congr 2
  have h1 : dW.pY ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pY_j0, Matrix.zero_mul]
  have h2 : dW.pX ⬝ (dW.j0 ⬝ y) = 0 := by rw [← Matrix.mul_assoc, HypDec.pX_j0, Matrix.zero_mul]
  have h3 : dW.p0 ⬝ (dW.j0 ⬝ y) = y := by rw [← Matrix.mul_assoc, HypDec.p0_j0, Matrix.one_mul]
  rw [dV.hO_coordS, dW.hO_coordT]
  simp only [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, Matrix.mul_assoc, HypDec.p0_jX, HypDec.p0_jY, HypDec.p0_j0,
    Matrix.mul_zero, Matrix.mul_one, h1, h2, h3]
  simp [pairS, pairT]

theorem isHalf_mul {a b c d : ℕ} {e : AE D} (A : Mx D a b) {y : Mx D b c} (C : Mx D c d) (hy : IsHalf e y) :
    IsHalf e (A ⬝ y ⬝ C) := by
  have h : e • y = y := Matrix.ext fun i j => hy i j
  intro i j
  have h2 : e • (A ⬝ y ⬝ C) = A ⬝ y ⬝ C := by rw [← Matrix.smul_mul, ← Matrix.mul_smul, h]
  exact congrFun (congrFun h2 i) j

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem mul_iota (b : AE D) (a : k) : b * p.ι a = p.ι (p.π b * a) := by
  have h1 : p.e * p.ι a = p.ι a := by rw [← p.ι_π, p.π_ι]
  have h2 := p.ι_π (b * p.ι a)
  rw [map_mul, p.π_ι, mul_left_comm, h1] at h2
  exact h2.symm

theorem rat_mul_iota {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (A : Matrix (Fin b) (Fin c) k) :
    rat R ⬝ (A.map p.ι : Mx D b c) = ((R.map p.pr * A).map p.ι : Mx D a c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, mul_iota, Place.pr]

theorem iota_mul_rat {a b c : ℕ} (A : Matrix (Fin a) (Fin b) k) (R : Matrix (Fin b) (Fin c) D.host.E) :
    (A.map p.ι : Mx D a b) ⬝ rat R = ((A * R.map p.pr).map p.ι : Mx D a c) := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rat, Matrix.mul_apply, Matrix.map_apply, map_sum, Place.pr]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm, mul_iota, mul_comm]

theorem map_pr_mul {a b c : ℕ} (R : Matrix (Fin a) (Fin b) D.host.E) (R' : Matrix (Fin b) (Fin c) D.host.E) :
    (R * R').map p.pr = R.map p.pr * R'.map p.pr :=
  Matrix.map_mul (f := p.π.comp (incA D))

theorem q_zero_projection_identities {W W₀ : HSp D} {σ : ℕ} (d : HypDec W W₀ σ) :
    d.q0.map p.pr * d.i₀.map p.pr = 1 ∧ d.q0.map p.pr * d.e.map p.pr = 0 ∧ d.q0.map p.pr * d.e'.map p.pr = 0 := by
  have h1 : d.q0 * d.i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact d.p0_j0)
  have h2 : d.q0 * d.e = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jX)
  have h3 : d.q0 * d.e' = 0 := rat_injective (by rw [rat_mul, rat_zero]; exact d.p0_jY)
  have z : p.pr 0 = 0 := map_zero (p.π.comp (incA D))
  have o : p.pr 1 = 1 := map_one (p.π.comp (incA D))
  refine ⟨?_, ?_, ?_⟩
  · rw [← map_pr_mul, h1, Matrix.map_one _ z o]
  · rw [← map_pr_mul, h2, Matrix.map_zero _ z]
  · rw [← map_pr_mul, h3, Matrix.map_zero _ z]

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem q_zero_jacobi_frame_projection {ρ : ℕ} (J : JacLev D ρ) (s hh : k) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c))
    (h : p.IsJacFrame J s hh G₀ FW) : J.d.q0.map p.pr * FW.β = fromCols G₀.β 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  obtain ⟨q1, q2, q3⟩ := q_zero_projection_identities p J.d
  have key : ∀ (E : Matrix (Fin J.W.rank) (Fin ρ) D.host.E), J.d.q0.map p.pr * E.map p.pr = 0 → ∀ (a : k) (i : Fin ρ)
      (j : Fin c), (∀ r, FW.β r (Sum.inr j) = a * p.pr (E r i)) → ∀ r, (J.d.q0.map p.pr * FW.β) r (Sum.inr j) = 0 := by
    intro E hE a i j hj r
    have := congrFun (congrFun hE r) i
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply] at this
    simp only [Matrix.mul_apply, Matrix.map_apply, hj]
    rw [← mul_zero a, ← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  ext r q
  rcases q with a | j
  · have : (J.d.q0.map p.pr * FW.β) r (Sum.inl a) = (J.d.q0.map p.pr * (J.d.i₀.map p.pr * G₀.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h0]
    rw [this, ← Matrix.mul_assoc, q1, Matrix.one_mul, fromCols_apply_inl]
  · rw [fromCols_apply_inr, Matrix.zero_apply]
    by_cases hj : j.val < ρ
    · exact key _ q2 _ ⟨j.val, hj⟩ j (hX ⟨j.val, hj⟩ j rfl) r
    · have := j.2
      exact key _ q3 _ ⟨2 * ρ - 1 - j.val, by omega⟩ j (hY ⟨2 * ρ - 1 - j.val, by omega⟩ j (by simp only []; omega)) r

theorem bessel_normal_frame_core_frame_part {ρ : ℕ} (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (FV : Frame k B.V.rank (n' ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (h : p.IsBesFrame B s FA FV) (j : Fin c)
    (hj : j.val = ρ) : B.d.i₀.map p.pr * F₀.β = FV.β.submatrix id (Sum.map id fun _ => j) := by
  obtain ⟨-, h0, -, hz, -⟩ := h
  ext r q
  rcases q with a | u
  · have : (B.d.i₀.map p.pr * F₀.β) r (Sum.inl a) = (B.d.i₀.map p.pr * (B.o.iA.map p.pr * FA.β)) r a := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp only [h₀.1]
    rw [this, ← Matrix.mul_assoc, ← map_pr_mul]
    exact (h0 r a).symm
  · cases u
    have h2 : p.pr ((B.d.i₀ *ᵥ vecB B.o B.ζ) r) = ∑ m, p.pr (B.d.i₀ r m) * p.pr (vecB B.o B.ζ m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Place.pr, Matrix.mulVec, dotProduct, map_sum, map_mul]
    simp only [Matrix.submatrix_apply, Sum.map_inr, id, hz j hj r, h2, Matrix.mul_apply, Matrix.map_apply, h₀.2,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem core_up {ρ : ℕ} (B : BesLev D ρ) (J : JacLev D ρ) (s hh : k) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n)
    (FW : Frame k J.W.rank (n ⊕ Fin c)) (h₀ : p.IsCoreFrame B s FA F₀) (hB : p.IsBesFrame B s FA FV)
    (hJ : p.IsJacFrame J s hh G₀ FW) (j : Fin (c + 1)) (hj : j.val = ρ) (t : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    J.d.p0 ⬝ (p.up FV FW t : WO B.V J.W) ⬝ B.d.j0 = p.up F₀ G₀ (t.submatrix Sum.inl (Sum.map id fun _ => j)) := by
  have h1 := q_zero_jacobi_frame_projection p J s hh G₀ FW hJ
  have h2 := bessel_normal_frame_core_frame_part p B s FA F₀ FV h₀ hB j hj
  have h3 : t * FV.γ * B.d.i₀.map p.pr = t.submatrix id (Sum.map id fun _ => j) * F₀.γ := by
    rw [← Matrix.mul_one (t * FV.γ * B.d.i₀.map p.pr), ← F₀.βγ, ← Matrix.mul_assoc, Matrix.mul_assoc _ _ F₀.β, h2]
    congr 1
    have : t * FV.γ * FV.β = t := by rw [Matrix.mul_assoc, FV.γβ, Matrix.mul_one]
    ext r q
    conv_rhs => rw [← this]
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]
  unfold Place.up HypDec.p0 HypDec.j0
  rw [rat_mul_iota, iota_mul_rat]
  congr 1
  rw [Matrix.mul_assoc FW.β, ← Matrix.mul_assoc _ FW.β, h1, Matrix.mul_assoc, h3]
  refine (Matrix.mul_assoc _ _ _).symm.trans ?_
  congr 1
  ext r q
  simp [Matrix.mul_apply, Fintype.sum_sum_type]

theorem submatrix_affPt (ρ : ℕ) (j : Fin (c + 1)) (hj : j.val = ρ) (x : Matrix n (n' ⊕ Unit) k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) :
    (affPt (ρ + 1) x.toCols₁ e + GlobalTheory.LocFlat.colAt n' c (ρ + 1) fun r => x r (Sum.inr ())).submatrix Sum.inl
      (Sum.map id fun _ => j) = x := by
  ext r q
  rcases q with a | u
  · simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free]
  · cases u
    simp [affPt, basePt, GlobalTheory.LocFlat.colAt, Free, hj]

theorem continuous_hO_up {S T : HSp D} (FS : Frame k S.rank n') (FT : Frame k T.rank n) (y : WO S T) :
    Continuous fun t => p.π (hO S T (p.up FS FT t) y) := by
  have hx : ∀ i j, Continuous fun t => p.up FS FT t i j := fun i j =>
    p.cont_ι.comp (((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_elem i j)
  refine p.cont_π.comp ?_
  exact continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
      continuous_finsetSum _ fun _ _ => continuous_const.mul (hx _ _)

theorem model_modul : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (y : WO B.V₀ J.W₀), IsHalf (cA D p.e) y → ∀ (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = ψ (symplO B.V₀ J.W₀ (p.up F₀ G₀ t) y) * Ψ.1 t) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ y (L₀ Ψ) := by
  intro D _ hLaws _ k _ _ _ _ _ _ p ν hν ψ ψk hψk ρ B J st s _ n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hTm L₀ hL₀ y hy
    Ψ Ψ' hΨ'
  have hψc : Continuous ψk := ((GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ st.weil.std).2.1 ψk hψk).1
  have hc : c = 2 * ρ := hJ.1
  obtain ⟨Φ, hΦSB, hΦ⟩ := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k ψk ν hψc hν n n' c (ρ + 1) (by omega)).1 (by omega)).2 Ψ.1 Ψ.2
  have hy' : IsHalf (cA D p.e) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)) := isHalf_mul J.d.j0 B.d.p0 hy
  have hχ : IsLocallyConstant fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) := by
    have h := (GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψk hψc).comp_continuous
      (continuous_hO_up p FV FW (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))
    have h4 := (GlobalTheory.T.heisenberg_frame_half_inverse D k p _ _ B.V J.W FV FW ψ ψk hψk).2.2.2.1
    have h5 : (fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y)))) = _ :=
      funext fun t => h4 t _ hy'
    rw [h5]
    exact h
  let Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) := ⟨Φ, hΦSB⟩
  let Φ₂ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
    ⟨fun t => ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.inc0 B.V₀ y))) * Φ t,
      hχ.mul hΦSB.1, hΦSB.2.mul_left⟩
  have h1 := hTm.modul _ hy' Φ₁ Φ₂ fun t => rfl
  have hMx : GlobalTheory.FinPl.MxAt (fun _ => True) y := fun i j =>
    ⟨congrFun (congrFun (GlobalTheory.SplitScalar.half_fin (GlobalTheory.SplitScalar.isSplitIdem_conj p.split) hy) i) j,
      Ideal.mem_iInf.2 fun w => (w.2 trivial).elim⟩
  have h2 := ((hLaws ψ fun _ => True).1 ρ B J st).Heisenberg₂.core (Tm Φ₁) (hTm.theta Φ₁) y hMx
  have h3 := hL₀ Φ₁ Ψ hΦ.symm
  have h4 : Ψ'.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ₂.1 := by
    funext x
    rw [hΨ' x, ← hΦ]
    unfold GlobalTheory.LocFlat.flCol GlobalTheory.RootEx.opE
    rw [← integral_const_mul]
    congr 1
    funext e
    have hj : ρ < c + 1 := by omega
    simp only [Φ₂]
    rw [symplectic_pairing_ext_zero_inc_zero, core_up p B J s _ FA F₀ FV G₀ FW h₀ hB hJ ⟨ρ, hj⟩ rfl, submatrix_affPt ρ ⟨ρ, hj⟩ rfl, mul_assoc]
  rw [← hL₀ Φ₂ Ψ' h4, h1, h2, h3]

end GlobalTheory.FlatBFLoc.ModelModul
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapFactorIntertwinesMultiplicationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMap_factor_intertwines_multiplication : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ J.W₀ → ℂ)), (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Ψ : SB (Matrix n (n' ⊕ Unit) k)), Ψ.1 = GlobalTheory.LocFlat.flCol ψk ν (ρ + 1) Φ.1 → flatBF st (Tm Φ) = L₀ Ψ) → ∀ (y : WO B.V₀ J.W₀), IsHalf (cA D p.e) y → ∀ (Ψ Ψ' : SB (Matrix n (n' ⊕ Unit) k)), (∀ t, Ψ'.1 t = ψ (symplO B.V₀ J.W₀ (p.up F₀ G₀ t) y) * Ψ.1 t) → L₀ Ψ' = heisO ψ B.V₀ J.W₀ y (L₀ Ψ) := by
  first | exact @GlobalTheory.FlatBFLoc.ModelModul.model_modul | exact GlobalTheory.FlatBFLoc.ModelModul.model_modul | (intros; apply GlobalTheory.FlatBFLoc.ModelModul.model_modul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLaws
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlatRow

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

def prH : D.host.E →+* k := p.π.comp (incA D)

theorem pr_eq : p.pr = prH p := rfl

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

theorem e_smul_map {m n : Type} (K : Matrix m n k) : p.e • K.map p.ι = K.map p.ι := by
  funext i j; exact e_mul_ι p (K i j)

theorem map_ι_π {m n : Type} (K : Matrix m n k) : (K.map p.ι).map p.π = K := by
  funext i j; exact p.π_ι (K i j)

theorem xi_ne : p.xi ≠ 0 := (map_ne_zero (prH p)).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)

theorem hz_ne {ρ : ℕ} (B : BesLev D ρ) : p.hz B ≠ 0 := (map_ne_zero (prH p)).2 B.line.2

theorem char_half {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) {a : AE D} (ha : p.e * a = a) :
    ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * a)) = ψk (p.π a) := by
  rw [h, p.ι_π, ha]; rfl

theorem infPart_conj_e : infPart D (cA D p.e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩ := p.split
  have h4 : cA D p.e * cA D p.e = cA D p.e := by rw [← map_mul, h1]
  have h5 : cA D p.e = cA D p.e * (p.e + cA D p.e) := by rw [mul_add, mul_comm (cA D p.e) p.e, h2, h4, zero_add]
  have h6 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 :=
    TensorProduct.zero_tmul _ _
  rw [h5, h3, map_mul, h6, mul_zero]

def xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : Mx D ρ S.rank :=
  adj (gA S ⬝ K.map p.ι)

theorem smul_xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : cA D p.e • xiPt p S K = xiPt p S K := by
  rw [xiPt, ← adj_smul, ← Matrix.mul_smul, e_smul_map]

theorem mxAt_xiPt (S : HSp D) {ρ : ℕ} (K : Matrix (Fin S.rank) (Fin ρ) k) : GlobalTheory.FinPl.MxAt (fun _ => True) (xiPt p S K) := by
  intro i j
  refine ⟨?_, ?_⟩
  · have h : cA D p.e * xiPt p S K i j = xiPt p S K i j := congrFun (congrFun (smul_xiPt p S K) i) j
    change infPart D _ = 0
    rw [← h, map_mul, infPart_conj_e, zero_mul]
  · exact Ideal.mem_iInf.2 fun w => (w.2 trivial).elim

section Pair

variable {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (K : Matrix (Fin V₀.rank) (Fin σ) k)

theorem isHalf_xiPt : IsHalf (cA D p.e) (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K))) := by
  have h : cA D p.e • (dW.jX ⬝ xiPt p V₀ K ⬝ dV.p0) = dW.jX ⬝ xiPt p V₀ K ⬝ dV.p0 := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, smul_xiPt]
  intro i j
  exact congrFun (congrFun h i) j

theorem hO_xiPt (x : WO V W) :
    hO V W x (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K))) = (dV.j0 ⬝ (K.map p.ι ⬝ (dW.pY ⬝ x))).trace := by
  rw [hO_eq_trace, HypDec.matrixExtendByZero_apply, HypDec.incX_apply, xiPt, dV.p0_eq, dW.pY_eq]
  simp only [adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, giA_gA_cancel]

theorem hO_incAdj_xiPt (y : Mx D V₀.rank σ) :
    hO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ (xiPt p V₀ K)) =
      (K.map p.ι ⬝ (incA D (-D.host.xi0⁻¹) • (adj y ⬝ gA V₀))).trace := by
  rw [hO_eq_trace, HypDec.incAdj_apply, HypDec.incY_apply, HypDec.incX_apply, xiPt]
  simp only [adj_mul, adj_adj, adj_gA, Matrix.mul_assoc, giA_gA_cancel, cancel₃ dW.gram_XY, Matrix.one_mul]

variable {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle}

theorem char_up (h : p.IsChar ψ ψk) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    (FV : Frame k V.rank Y') (FW : Frame k W.rank Y) (t : Matrix Y Y' k) :
    ψ (symplO V W (p.up FV FW t) (dV.ext0 W (dW.incX V₀ (xiPt p V₀ K)))) =
      ψk ((FV.γ * (dV.j0.map p.π * K) * (dW.pY.map p.π * FW.β) * t).trace) := by
  rw [symplO, hO_xiPt, char_half p h]
  · congr 2
    rw [AddMonoidHom.map_trace, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, map_ι_π, Place.up, map_ι_π]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
  · rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.mul_smul, ← Matrix.smul_mul, e_smul_map]

theorem char_incAdj (h : p.IsChar ψ ψk) (y : Mx D V₀.rank σ) :
    ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ (xiPt p V₀ K))) =
      ψk (-p.xi⁻¹ * (K * (adj y ⬝ gA V₀).map p.π).trace) := by
  rw [symplO, hO_incAdj_xiPt, char_half p h]
  · congr 2
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, map_mul, AddMonoidHom.map_trace, Matrix.map_mul, map_ι_π]
    congr 1
    change prH p _ = -(prH p _)⁻¹
    rw [map_neg, map_inv₀]
  · rw [← smul_eq_mul, ← Matrix.trace_smul, ← Matrix.smul_mul, e_smul_map]

end Pair

theorem mul_col {l m n Y : Type} [Fintype m] {P : Matrix l m k} {X : Matrix m n k} {M : Matrix m Y k} {j : Y} {i : n} {a : k}
    (h : ∀ r, M r j = a * X r i) (i₀ : l) : (P * M) i₀ j = a * (P * X) i₀ i := by
  simp only [Matrix.mul_apply, h, Finset.mul_sum, mul_left_comm]

theorem jac_row {ρ : ℕ} {J : JacLev D ρ} {s hh : k} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    {G₀ : Frame k J.W₀.rank n} {FW : Frame k J.W.rank (n ⊕ Fin c)} (h : p.IsJacFrame J s hh G₀ FW) (i : Fin ρ) (l : Fin c)
    (hl : l.val + i.val + 1 = 2 * ρ) (r : n ⊕ Fin c) :
    (J.d.pY.map p.π * FW.β) i r = if r = Sum.inr l then s * (hh / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) else 0 := by
  obtain ⟨hc, h0, hX, hY⟩ := h
  rcases r with a | j
  · rw [if_neg Sum.inl_ne_inr, mul_col (a := 1) (X := J.d.j0.map p.π * G₀.β) (i := a) (fun r => by rw [one_mul]; exact h0 r a),
      ← Matrix.mul_assoc, ← Matrix.map_mul, J.d.pY_j0]
    simp
  · by_cases hj : j.val < ρ
    · have hne : (Sum.inr j : n ⊕ Fin c) ≠ Sum.inr l := fun e => by
        have := congrArg Fin.val (Sum.inr_injective e); omega
      rw [if_neg hne, mul_col (X := J.d.jX.map p.π) (i := ⟨j.val, hj⟩) (hX ⟨j.val, hj⟩ j rfl), ← Matrix.map_mul, J.d.pY_jX]
      simp
    · have hj' : 2 * ρ - 1 - j.val < ρ := by have := j.2; omega
      rw [mul_col (X := J.d.jY.map p.π) (i := ⟨_, hj'⟩) (hY ⟨_, hj'⟩ j (by have := j.2; simp only; omega)), ← Matrix.map_mul,
        J.d.pY_jY, Matrix.map_apply, Matrix.one_apply]
      by_cases e : j = l
      · have e' : i = ⟨_, hj'⟩ := Fin.ext (by subst e; simp only; omega)
        rw [if_pos e', if_pos (congrArg _ e), map_one, mul_one, ← e']
      · have e' : i ≠ ⟨_, hj'⟩ := fun e' => e (Fin.ext (by have := congrArg Fin.val e'; have := j.2; simp only at *; omega))
        rw [if_neg e', if_neg (fun x => e (Sum.inr_injective x)), map_zero, mul_zero]

theorem core_val {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n] {FA : Frame k B.A.rank n}
    {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} (h : p.IsCoreFrame B s FA F₀) (i : Fin ρ) (q : n ⊕ Unit) :
    ((adj (yZero B.V₀ ρ (vecB B.o B.ζ)) ⬝ gA B.V₀).map p.π * F₀.β) i q =
      if i.val + 1 = ρ ∧ q = Sum.inr () then -(s * p.hz B) else 0 := by
  have h1 : ∀ x, (adj (yZero B.V₀ ρ (vecB B.o B.ζ)) ⬝ gA B.V₀).map p.π i x =
      -(if i.val + 1 = ρ then 1 else 0) * prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) := by
    intro x
    rw [← Matrix.vecMul_vecMul, ← Matrix.star_mulVec]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.map_apply, Matrix.mul_apply, adj, yZero, zEll, Matrix.transpose_apply, Matrix.neg_apply,
      Matrix.vecMulVec_apply, ell, ratV, Matrix.vecMul, dotProduct, map_sum, Finset.mul_sum, gA, rat]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs
    · rw [mul_one, map_neg, GlobalTheory.DualPairCheck.cA_incA, neg_mul, ← map_mul, map_neg, neg_one_mul]; rfl
    · simp
  rw [Matrix.mul_apply]
  simp only [h1, mul_assoc, ← Finset.mul_sum]
  rcases q with a | ⟨⟨⟩⟩
  · have h2 : ∀ y, ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * prH p (B.o.iA x y) = 0 := by
      intro y
      have : ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) ᵥ* B.o.iA) y = 0 := by
        rw [Matrix.vecMul_vecMul, B.o.orth, Matrix.vecMul_zero]; rfl
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← map_mul, ← map_sum]
      rw [← map_zero (prH p), ← this]; rfl
    have h3 : ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * F₀.β x (Sum.inl a) = 0 := by
      have e : ∀ x, F₀.β x (Sum.inl a) = ∑ y, prH p (B.o.iA x y) * FA.β y a := fun x => h.1 x a
      simp only [e, Finset.mul_sum, ← mul_assoc]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, h2, zero_mul, Finset.sum_const_zero]
    rw [h3]; simp
  · have h3 : ∑ x, prH p ((star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) x) * F₀.β x (Sum.inr ()) = s * p.hz B := by
      have : star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ = (star B.ζ ᵥ* (B.o.iBᴴ * B.V₀.gram)) ⬝ᵥ vecB B.o B.ζ := by
        rw [← B.o.isoB, vecB, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Place.hz, this, pr_eq, dotProduct, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [h.2, map_mul, pr_eq]; ring
    rw [h3]; by_cases e : i.val + 1 = ρ <;> simp [e]

theorem core_col {ρ : ℕ} {B : BesLev D ρ} {s : k} {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {FA : Frame k B.A.rank n}
    {F₀ : Frame k B.V₀.rank (n ⊕ Unit)} {FV : Frame k B.V.rank (n ⊕ Fin c)} (h₀ : p.IsCoreFrame B s FA F₀)
    (h : p.IsBesFrame B s FA FV) (q : n ⊕ Fin c) (hq : ∀ i, q = Sum.inr i → i.val = ρ) (x : Fin B.V.rank) :
    (B.d.j0.map p.π * F₀.β) x (q.map id fun _ => ()) = FV.β x q := by
  rcases q with a | i
  · rw [h.2.1, pr_eq, Matrix.map_mul, Matrix.mul_assoc,
      mul_col (a := 1) (X := B.o.iA.map (prH p) * FA.β) (i := a) (fun r => by rw [one_mul]; exact h₀.1 r a), one_mul]
    rfl
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [h.2.2.2.1 i (hq i rfl), pr_eq, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, mul_left_comm]
    exact congrArg _ (h₀.2 y)

theorem trace_single {m n l : Type} [Fintype m] [Fintype n] [DecidableEq n] [Fintype l] [DecidableEq l] (M : Matrix m n k) (q : n)
    (i : l) (a : k) (N : Matrix l m k) : (M * Matrix.single q i a * N).trace = a * (N * M) i q := by
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, smul_eq_mul]

theorem flatBF_mul_row : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  intro D hF hL _ k _ _ _ _ _ _ p ν _ ψ ψk hch ρ B J st s hs n n' _ _ _ _ c FA F₀ FV G₀ FW h₀ hB hJ Tm hT r q hr b Φ Φ' hΦ
  obtain ⟨l, rfl, hl, hq⟩ := hr
  have hc := hJ.1
  have hi : 2 * ρ - 1 - l.val < ρ := by have := l.2; omega
  obtain ⟨i, hli⟩ : ∃ i : Fin ρ, l.val + i.val + 1 = 2 * ρ := ⟨⟨_, hi⟩, by have := l.2; simp only; omega⟩
  have hxi := xi_ne p
  have hhz := hz_ne p B
  obtain ⟨κ, hκ⟩ : ∃ κ, κ = s * (p.hz B / p.xi) * (-1 / p.xi) ^ (ρ - 1 - i.val) := ⟨_, rfl⟩
  have hκ0 : κ ≠ 0 := by
    rw [hκ]; exact mul_ne_zero (mul_ne_zero hs (div_ne_zero hhz hxi)) (pow_ne_zero _ (div_ne_zero (by simp) hxi))
  obtain ⟨K, hK⟩ : ∃ K, K = F₀.β * Matrix.single (q.map id fun _ => ()) i (b / κ) := ⟨_, rfl⟩
  have h1 : ∀ t, ψ (symplO B.V J.W (p.up FV FW t) (B.d.ext0 J.W (J.d.incX B.V₀ (xiPt p B.V₀ K)))) =
      ψk (b * t (Sum.inr l) q) := by
    intro t
    have e : FV.γ * (B.d.j0.map p.π * K) * (J.d.pY.map p.π * FW.β) * t =
        FV.γ * (B.d.j0.map p.π * F₀.β) * Matrix.single (q.map id fun _ => ()) i (b / κ) * (J.d.pY.map p.π * FW.β * t) := by
      simp only [hK, Matrix.mul_assoc]
    rw [char_up p B.d J.d K hch, e, trace_single, ← Matrix.mul_assoc _ FV.γ,
      mul_col (a := 1) (X := FV.β) (i := q) (fun x => by rw [one_mul]; exact core_col p h₀ hB q hq x), one_mul,
      Matrix.mul_assoc _ FV.γ, FV.γβ, Matrix.mul_one, Matrix.mul_apply]
    simp only [jac_row p hJ i l hli, ← hκ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← mul_assoc, div_mul_cancel₀ _ hκ0]
  have h2 : ψ (symplO B.V₀ J.W (J.d.incAdj B.V₀ (yZero B.V₀ ρ (vecB B.o B.ζ))) (J.d.incX B.V₀ (xiPt p B.V₀ K))) =
      ψk (b * GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr l) q) := by
    rw [char_incAdj p J.d K hch, hK, trace_single, core_val p h₀]
    congr 2
    rcases q with a | j
    · simp [GlobalTheory.RootEx.basePt]
    · have hj := hq j rfl
      by_cases e : i.val + 1 = ρ
      · have e1 : l.val = j.val := by omega
        have e2 : ρ - 1 - i.val = 0 := by omega
        rw [e2, pow_zero, mul_one] at hκ
        simp only [GlobalTheory.RootEx.basePt, e, e1, Sum.map_inr, and_self, if_true, fromBlocks_apply₂₂, of_apply, hκ]
        field_simp
      · have e1 : l.val ≠ j.val := by omega
        simp [GlobalTheory.RootEx.basePt, e, e1]
  obtain ⟨a, ha⟩ : ∃ a : ℂ, a = ψk (b * GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) (Sum.inr l) q) := ⟨_, rfl⟩
  have ha0 : a ≠ 0 := by rw [ha]; exact Circle.coe_ne_zero _
  have h3 := hT.modul _ (isHalf_xiPt p B.d J.d K) Φ (a • Φ') fun t => by
    rw [h1, Submodule.coe_smul, Pi.smul_apply, hΦ, smul_eq_mul, ← mul_assoc, ha, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
    congr 3
    ring
  have h4 := ((hL ψ fun _ => True).1 ρ B J st).Heisenberg₂.iso _ (hT.theta Φ) _ (mxAt_xiPt p B.V₀ K)
  rw [← h3, h2, ← ha, map_smul, (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J st _ _ a (hT.theta Φ') (hT.theta Φ')).2] at h4
  exact smul_right_injective _ ha0 h4

end GlobalTheory.FlatRow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatBesselToFourierJacobiRowMulLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_bessel_to_fourierJacobi_row_mul_laws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatRow.flatBF_mul_row | exact GlobalTheory.FlatRow.flatBF_mul_row | (intros; apply GlobalTheory.FlatRow.flatBF_mul_row <;> assumption)
end
end
