module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetClosedOpenSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationEquivariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPolyBallOfCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesOpenCell

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesClosedCell
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesClosedCell
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocC

open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl GlobalTheory.CompanionTheory.MirFourier ValuativeRel

attribute [local instance] instMSpi instBSpi

section Final

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)}

abbrev thL (ψ : AddChar k Circle) (s : kˣ) : Lball k i t s →* ℂˣ :=
  (mirChar k ψ ((i + 1) + t)).comp (Subgroup.inclusion (Lball_le s))

theorem thL_uEl (ψ : AddChar k Circle) (s : kˣ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k)
    (h : uEl k i t c d ∈ Lball k i t s) :
    thL ψ s ⟨uEl k i t c d, h⟩ = Circle.toUnits (ψ (d (Fin.last t))) :=
  mirChar_uEl ψ i t c d (Lball_le s h)

theorem isOpen_ker_thL (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) :
    IsOpen ((thL (i := i) (t := t) ψ s).ker : Set (Lball k i t s)) :=
  (GlobalTheory.CompanionTheory.BZPhiPG.Grp.mirChar_ker_open ψ hψ ((i + 1) + t)).preimage
    (show Continuous (Subgroup.inclusion (Lball_le (i := i) (t := t) s)) from continuous_subtype_val.subtype_mk _)

theorem iF_sub (ψ : AddChar k Circle) (hψ : Continuous ψ) (a b : XS τ σ) : iF ψ (a - b) = iF ψ a - iF ψ b :=
  (iL ψ hψ).map_sub a b

theorem iF_zero (ψ : AddChar k Circle) (hψ : Continuous ψ) : iF ψ (0 : XS τ σ) = 0 :=
  (iL ψ hψ).map_zero

theorem gen (ψ : AddChar k Circle) (hψ : Continuous ψ) (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v - ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • v) =
      ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • (rU τ σ (Multiplicative.ofAdd c) (iF ψ v) - iF ψ v) := by
  have a1 := iF_smul ψ hψ ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) v
  have a2 := iF_translate ψ hψ v c d
  exact (iF_sub ψ hψ _ _).trans ((congrArg₂ (fun a b => a - b) a2 a1).trans (smul_sub _ _ _).symm)

theorem thL_eq (ψ : AddChar k Circle) (s : kˣ) (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (e : l = uEl k i t c d) :
    thL ψ s ⟨l, hl⟩ = Circle.toUnits (ψ (d (Fin.last t))) := by
  subst e
  exact thL_uEl ψ s c d hl

theorem mem_of_eq {V : Type} [AddCommGroup V] [Module ℂ V] (K : Submodule ℂ V) {z y : V} (h : z = y) (hy : y ∈ K) : z ∈ K :=
  h ▸ hy

theorem gen_mem (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (l : Mir k ((i + 1) + (t + 1))) (hl : l ∈ Lball k i t s)
    (v : XS τ σ) :
    iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v - ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) • v) ∈
      twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  have h := exists_of_mem_Lball hl
  refine Exists.elim h fun c h => Exists.elim h fun d h => ?_
  have hc := h.1
  have e := h.2.2
  have e1 : cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) l v = cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uEl k i t c d) v :=
    congrArg (fun x => cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) x v) e
  have e2 : ((thL ψ s ⟨l, hl⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_eq ψ s l hl c d e)
  have e3 := congrArg₂ (fun (a : XS τ σ) (b : ℂ) => iF ψ (a - b • v)) e1 e2
  refine mem_of_eq _ (e3.trans (gen ψ hψ c d v)) (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, hc⟩, iF ψ v, ?_⟩))
  simp

theorem iF_twKer (ψ : AddChar k Circle) (hψ : Continuous ψ) (s : kˣ) (v : XS τ σ)
    (hv : v ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s)) :
    iF ψ v ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
  unfold twKer at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine Exists.elim hx fun l h => Exists.elim h fun v h => ?_
    exact mem_of_eq _ (congrArg (iF ψ) h) (gen_mem ψ hψ s l.1 l.2 v)
  | zero => exact mem_of_eq _ (iF_zero ψ hψ) (zero_mem _)
  | add x y _ _ hx hy => exact mem_of_eq _ (iF_add ψ hψ x y) (add_mem hx hy)
  | smul c x _ hx => exact mem_of_eq _ (iF_smul ψ hψ c x) (Submodule.smul_mem _ _ hx)

theorem eig_eval (ψ : AddChar k Circle) (s : kˣ) (g : XS τ σ)
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (c : Fin (i + 1) → k) (d : Fin (t + 1) → k) (hc : Multiplicative.ofAdd c ∈ polyBall (i + 1) s)
    (hd : Multiplicative.ofAdd d ∈ polyBall (t + 1) s) (x : Mir k ((i + 1) + t + 1)) :
    evX g (x * uEl k i t c d) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) • evX g x := by
  have hm := uEl_mem_Lball hc hd
  have e := congrArg (fun w : XS τ σ => evX w x) (g2 ⟨_, hm⟩)
  have e2 : ((thL ψ s ⟨_, hm⟩ : ℂˣ) : ℂ) = ((Circle.toUnits (ψ (d (Fin.last t))) : ℂˣ) : ℂ) :=
    congrArg _ (thL_uEl ψ s c d hm)
  exact (evX_cInd g _ x).symm.trans (e.trans ((evX_smul _ g x).trans (congrArg (fun b : ℂ => b • evX g x) e2)))

theorem supp_of (s : kˣ) (f : XS τ σ)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (l : Mir k ((i + 1) + t + 1)) (hl : l ∈ Lball k i t s) (d : Fin (t + 1) → k)
    (hne : evX f (dEmb k i t d * 1 * l) ≠ 0) : Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
  obtain ⟨c, d₁, hc, hd₁, rfl⟩ := exists_of_mem_Lball hl
  rw [dEmb_mul_uEl, evX_left] at hne
  have h3 : evX f (dEmb k i t (d + d₁) * 1) ≠ 0 := by
    intro h0
    exact hne (by rw [h0, map_zero])
  have h4 := (polyBall (t + 1) s).mul_mem (hF _ h3) ((polyBall (t + 1) s).inv_mem hd₁)
  have e : Multiplicative.ofAdd (d + d₁) * (Multiplicative.ofAdd d₁)⁻¹ = Multiplicative.ofAdd d := by
    rw [ofAdd_add, mul_inv_cancel_right]
  rwa [e] at h4

theorem avgVanish_of_data (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (s : kˣ) (hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1)
    (hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s)
    (g : XS τ σ) (g1 : f - g ∈ twKer (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (Lball k i t s) (thL ψ s))
    (g2 : ∀ l : Lball k i t s, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (l : Mir k ((i + 1) + t + 1)) g = ((thL ψ s l : ℂˣ) : ℂ) • g)
    (g3 : ∀ x : Mir k ((i + 1) + t + 1), evX g x ≠ 0 → ∃ l ∈ Lball k i t s, evX f (x * l) ≠ 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  have hsupp : ∀ d : Fin (t + 1) → k, evX g (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s := by
    intro d hd
    refine Exists.elim (g3 _ hd) fun l h => ?_
    exact supp_of s f hF l h.1 d h.2
  have hk : iF ψ g ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := by
    have h5 := iF_twKer ψ hψ s (f - g) g1
    have e : iF ψ g = iF ψ f - iF ψ (f - g) := by
      have := iF_sub ψ hψ f g
      rw [this, sub_sub_cancel]
    exact mem_of_eq _ e (sub_mem hz h5)
  refine ⟨Lball k i t s, Lball_le s, isCompact_Lball s, g, g1, g2, fun u hu => ?_⟩
  refine Exists.elim (exists_uEl i t u hu) fun c h => Exists.elim h fun d e => ?_
  have h7 := vanish_of_eigen ψ hτ hσ s g (eig_eval ψ s g g2) hsupp hk c d
  have e2 : (1 : Mir k ((i + 1) + t + 1)) * u = uEl k i t c d := by rw [one_mul, e]
  exact (congrArg (evX g) e2).trans h7

theorem avgVanish_one (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (hq : qC τ σ (iF ψ f) = 0) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f 1 := by
  obtain ⟨s₁, h₁⟩ := exists_polyBall_of_qC _ hq
  obtain ⟨s₂, h₂⟩ := exists_polyBall_of_compact
    (GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f 1).2
  obtain ⟨s, a, b⟩ := exists_val_ge s₁ s₂
  have hz : iF ψ f ∈ twKer (rU τ σ) (polyBall (i + 1) s) 1 := twKer_one_mono _ (polyBall_mono _ a) h₁
  have hF : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * 1) ≠ 0 → Multiplicative.ofAdd d ∈ polyBall (t + 1) s :=
    fun d hd => polyBall_mono _ b (h₂ d (subset_tsupport _ hd))
  have hg := exists_avg (HPG k (i + 1) (t + 1)) (sigX τ σ) (Lball k i t s) (isCompact_Lball s)
    (thL ψ s) (isOpen_ker_thL ψ hψ s) f
  exact Exists.elim hg fun g h => avgVanish_of_data ψ hψ hτ hσ f s hz hF g h.1 h.2.1 h.2.2

theorem mirChar_sEmb_conj (ψ : AddChar k Circle) {n : ℕ} (m : Mir k n) (u : MirUin k (n + 1))
    (h : (sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m ∈ MirUin k (n + 1)) :
    mirChar k ψ n ⟨_, h⟩ = mirChar k ψ n u := by
  obtain ⟨w, hw⟩ := (Subgroup.mem_subgroupOf.1 u.2 : ((u : Mir k (n + 1)) : GL (Fin (n + 2)) k) ∈ MirU k (n + 1))
  rw [mirChar_eq k ψ n u w hw.symm]
  let mi : GL (Fin (n + 1)) k := ((m⁻¹ : Mir k n) : GL (Fin (n + 1)) k)
  have e0 : (((sEmb k n m)⁻¹ : Mir k (n + 1)) : GL (Fin (n + 2)) k) = glEmb k (n + 1) mi := by
    rw [← map_inv]
    rfl
  have e1 : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) = (glEmb k (n + 1) mi)⁻¹ := by
    rw [← e0]
    simp
  have e : (((sEmb k n m)⁻¹ * (u : Mir k (n + 1)) * sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd ((mi : Matrix _ _ k).mulVec w.toAdd)) := by
    simp only [Subgroup.coe_mul]
    rw [e0, e1, ← hw, glEmb_mul_unip', mul_inv_cancel_right]
  rw [mirChar_eq k ψ n ⟨_, h⟩ _ e, toAdd_ofAdd,
    mulVec_last_of_mem k mi (m⁻¹ : Mir k n).2 w.toAdd]

theorem avgVanish_cell (ψ : AddChar k Circle) (hψ : Continuous ψ) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (f : XS τ σ) (h0 : eC ψ f = 0) (h : Mir k ((i + 1) + t + 1)) (hh : h ∈ HPG k (i + 1) (t + 1))
    (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f
      (h * dEmb k i t d * sEmb k ((i + 1) + t) m) := by
  have hq : qC τ σ (intC ψ f (sEmb k _ m)) = 0 := by
    have h1 : ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) • qC τ σ (intC ψ f (sEmb k _ m)) = 0 := congrFun h0 m
    exact (smul_eq_zero.1 h1).resolve_left (Units.ne_zero _)
  have hp : phi ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) =
      fun d => (((Circle.toUnits (ψ (d (Fin.last t))))⁻¹ : ℂˣ) : ℂ) • evX f (dEmb k i t d * sEmb k _ m) := by
    funext d
    simp only [phi]
    rw [evX_cInd, mul_one]
    rfl
  have hi : iF ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f) = intC ψ f (sEmb k _ m) :=
    congrArg (GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1))) hp
  have A1 := avgVanish_one ψ hψ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k _ m) f)
    ((congrArg (qC τ σ) hi).trans hq)
  have hU : ∀ u ∈ MirUin k ((i + 1) + t + 1), sEmb k _ m * u * (sEmb k _ m)⁻¹ ∈ MirUin k ((i + 1) + t + 1) :=
    fun u hu => GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin _ ⟨u, hu⟩
  have hU' : ∀ u ∈ MirUin k ((i + 1) + t + 1), (sEmb k _ m)⁻¹ * u * sEmb k _ m ∈ MirUin k ((i + 1) + t + 1) := by
    intro u hu
    have := GlobalTheory.CompanionTheory.BZMirSeq.conj_mem_MirUin (sEmb k _ m)⁻¹ ⟨u, hu⟩
    rwa [inv_inv] at this
  have A2 := avgVanish_conj _ _ _ _ (sEmb k _ m) hU hU' (fun u h => mirChar_sEmb_conj ψ m u h) f A1
  exact avgVanish_left _ _ _ _ f _ _ h hh (hU' _ (uEl_mem i t 0 d)) A2

end Final

theorem avgVanish_of_mem_Cl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eC ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∈ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  intro k _ _ _ _ i t ψ hψ τ σ hτ hσ f h0 p hp
  refine Exists.elim ((GlobalTheory.CompanionTheory.BZPhiPG.Cells.cells k i t).1 p hp) fun h hh =>
    Exists.elim hh.2 fun d hd => Exists.elim hd fun m e => ?_
  exact (congrArg (AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f) e).mpr
    (avgVanish_cell ψ hψ hτ hσ f h0 h hh.1 d m)

end GlobalTheory.CompanionTheory.BZPhiPG.LocC

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageVanishesClosedCellStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.average_vanishes_closed_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (h0 : eC ψ f = 0)
    (p : Mir k ((i + 1) + t + 1)) (hp : p ∈ Cl k i t),
  AvgVanish (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t)) f p := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl | exact GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.LocC.avgVanish_of_mem_Cl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationVanishingOnOpenStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedEvaluationVanishingOnOpen
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.Off

variable {k : Type} [Field k]

theorem sEmb_row (n : ℕ) (m : Mir k n) (j : Fin (n + 1 + 1)) :
    (((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
      (Fin.castSucc (Fin.last n)) j = (1 : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hs : ((sEmb k n m : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmb k (n + 1) (m : GL (Fin (n + 1)) k) := rfl
  have hm : Matrix.vecMul (GlobalTheory.BZMir.eLast k n) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.eLast k n := m.2
  rw [GlobalTheory.BZMir.vecMul_eLast] at hm
  rw [hs]
  show GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
    (Fin.castSucc (Fin.last n)) j = _
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last]
    rw [Matrix.one_apply_ne (Fin.castSucc_lt_last _).ne]
  · simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc]
    rw [hm]
    by_cases hj : j' = Fin.last n
    · subst hj
      simp [GlobalTheory.BZMir.eLast]
    · rw [Matrix.one_apply_ne (fun e => hj (Fin.castSucc_injective _ e).symm)]
      simp [GlobalTheory.BZMir.eLast, Pi.single_apply, hj]

theorem dEmb_mul_sEmb_mem_Cl (i t : ℕ) (d : Fin (t + 1) → k) (m : Mir k ((i + 1) + t)) :
    dEmb k i t d * sEmb k _ m ∈ Cl k i t := by
  simp only [Cl, Set.mem_ofPred_eq]
  intro c
  rw [_root_.mul_inv_rev, ← map_inv, Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
  simp_rw [sEmb_row]
  rw [← Matrix.mul_apply, Matrix.one_mul]
  show ((1 : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) -
      GlobalTheory.BZMir.colMat k (i + 1 + (t + 1)) (Fin.append 0 d)) _ _ = 0
  rw [Matrix.sub_apply]
  have hRC : (Fin.last (i + 1 + t)).castSucc ≠ (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  have hCL : (Fin.castLE (by omega) c : Fin (i + 1 + t + 1 + 1)) ≠ Fin.last (i + 1 + (t + 1)) := by
    intro e
    have := congrArg Fin.val e
    simp at this
    omega
  rw [Matrix.one_apply_ne hRC]
  simp [GlobalTheory.BZMir.colMat, hCL]

end GlobalTheory.CompanionTheory.BZPhiPG.Off


open GlobalTheory.CompanionTheory.BZPhiPG.Off in
theorem GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
    eC ψ f = 0 := by
  intro k _ _ _ _ i t ψ τ σ hτ hσ f hf
  funext m
  have hz : ∀ d : Fin (t + 1) → k, evX f (dEmb k i t d * sEmb k (i + 1 + t) m) = 0 :=
    fun d => hf _ (dEmb_mul_sEmb_mem_Cl i t d m)
  have hint : intC ψ f (sEmb k (i + 1 + t) m) = 0 := by
    unfold intC
    simp only [hz, smul_zero]
    unfold GlobalTheory.CompanionTheory.Rodier.smInt
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w = 0
    · rw [hw, smul_zero]
    · have hpre : ((fun _ => (0 : TensorProduct ℂ τ.V σ.V)) : (Fin (t + 1) → k) → TensorProduct ℂ τ.V σ.V) ⁻¹' {w} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h0 => hw h0.symm
      rw [hpre, MeasureTheory.measure_empty]
      simp
  simp only [eC, hint, map_zero, smul_zero, Pi.zero_apply]

end
end

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_evaluation_vanishing_on_open : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  eC ψ f = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | exact GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.eC_eq_zero_of_vanish <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariant
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariant
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPhiPG.TwO

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


variable (k) in
def uM (n : ℕ) (w : Fin n → k) : Mir k n :=
  ⟨unip k n (Multiplicative.ofAdd w), MirU_le_Mir k _ ⟨_, rfl⟩⟩

theorem uM_add (n : ℕ) (v w : Fin n → k) : uM k n (v + w) = uM k n v * uM k n w := by
  apply Subtype.ext
  show unip k n (Multiplicative.ofAdd (v + w)) = unip k n (Multiplicative.ofAdd v) * unip k n (Multiplicative.ofAdd w)
  rw [ofAdd_add, map_mul]

theorem levi_mul_uM (n : ℕ) (g : GL (Fin n) k) (v : Fin n → k) :
    levi k n g * uM k n v = uM k n ((g : Matrix (Fin n) (Fin n) k).mulVec v) * levi k n g := by
  apply Subtype.ext
  exact glEmb_mul_unip' k n g (Multiplicative.ofAdd v)

theorem ePG_true_val (i t : ℕ) (b : Fin t) : ((ePG i t ⟨true, b⟩ : Fin (i + t + 1)) : ℕ) = i + b := by
  simp [ePG]

theorem ePG_false_castSucc_val (i t : ℕ) (a : Fin i) :
    ((ePG i t ⟨false, Fin.castSucc a⟩ : Fin (i + t + 1)) : ℕ) = a := by
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem piPerm_last (i t : ℕ) : piPerm i t (Fin.last ((i + 1) + t)) = Fin.castAdd (t + 1) (Fin.last i) := by
  have h1 : (finCongr (by omega : (i + 1) + t + 1 = i + (t + 1) + 1)) (Fin.last ((i + 1) + t)) = Fin.last (i + (t + 1)) :=
    Fin.ext (by simp)
  have h2 : (ePG i (t + 1)).symm (Fin.last (i + (t + 1))) = ⟨false, Fin.last i⟩ := by
    rw [Equiv.symm_apply_eq, ePG_false_last]
  show eGP (i + 1) t ((ePG i (t + 1)).symm ((finCongr _) (Fin.last ((i + 1) + t)))) = _
  rw [h1, h2]
  apply Fin.ext
  simp [eGP, stdSum]

def cVec (i t : ℕ) (c : Fin (i + 1) → k) : Fin ((i + 1) + (t + 1)) → k := Fin.append c (0 : Fin (t + 1) → k)

theorem unip_entry (n : ℕ) (w : Fin n → k) (a b : Fin (n + 1)) :
    ((uM k n w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) a b + colMat k n w a b := rfl

theorem ePG_true_ne_last (i t : ℕ) (b : Fin t) : ePG i t ⟨true, b⟩ ≠ Fin.last (i + t) := by
  intro h
  have := congrArg Fin.val h
  rw [ePG_true_val] at this
  simp at this
  omega

theorem ePG_true_eq_natAdd (i t : ℕ) (b : Fin (t + 1)) :
    ePG (i + 1) (t + 1) ⟨true, b⟩ = Fin.castSucc (Fin.natAdd (i + 1) b) := by
  apply Fin.ext
  rw [ePG_true_val]
  simp

theorem ePG_false_eq_castAdd (i t : ℕ) (a : Fin (i + 1)) :
    ePG (i + 1) (t + 1) ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd (t + 1) a) := by
  apply Fin.ext
  rw [ePG_false_castSucc_val]
  simp

theorem uM_mem_HPG (i t : ℕ) (c : Fin (i + 1) → k) : uM k _ (cVec i t c) ∈ HPG k (i + 1) (t + 1) := by
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k) ∈ parab k (ePG (i + 1) (t + 1))
  rw [mem_parab_iff]
  rintro (_ | _) (_ | _) x y hab
  · exact absurd hab (by decide)
  · exact absurd hab (by decide)
  · rw [unip_entry]
    have hne : ePG (i + 1) (t + 1) ⟨true, x⟩ ≠ ePG (i + 1) (t + 1) ⟨false, y⟩ := by
      intro h
      simpa using (ePG (i + 1) (t + 1)).injective h
    rw [Matrix.one_apply_ne hne, zero_add]
    simp only [colMat]
    split_ifs with hl
    · rw [ePG_true_eq_natAdd, Fin.lastCases_castSucc, cVec, Fin.append_right]
      rfl
    · rfl
  · exact absurd hab (by decide)

theorem pgProj_fst (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).1 = uM k (i + 1) c := by
  apply Subtype.ext
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨false, a⟩) (ePG (i + 1) (t + 1) ⟨false, b⟩) =
    (1 : Matrix (Fin (i + 1 + 1)) (Fin (i + 1 + 1)) k) a b + colMat k (i + 1) c a b
  rw [unip_entry]
  congr 1
  · by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro h
      apply hab
      simpa using (ePG (i + 1) (t + 1)).injective h
  · simp only [colMat]
    by_cases hb : b = Fin.last (i + 1)
    · subst hb
      rw [if_pos (ePG_false_last _ _), if_pos rfl]
      induction a using Fin.lastCases with
      | last => rw [ePG_false_last, Fin.lastCases_last, Fin.lastCases_last]
      | cast a =>
        rw [ePG_false_eq_castAdd, Fin.lastCases_castSucc, Fin.lastCases_castSucc, cVec, Fin.append_left]
    · rw [if_neg (fun h => hb ((ePG_false_eq_last_iff _ _ _).1 h)), if_neg hb]

theorem pgProj_snd (i t : ℕ) (c : Fin (i + 1) → k) :
    (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩).2 = 1 := by
  apply Units.ext
  ext a b
  show ((uM k _ (cVec i t c) : Mir k _) : GL _ k).val (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) =
    (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) k) a b
  rw [unip_entry]
  have h0 : colMat k _ (cVec i t c) (ePG (i + 1) (t + 1) ⟨true, a⟩) (ePG (i + 1) (t + 1) ⟨true, b⟩) = 0 := by
    simp only [colMat]
    rw [if_neg (ePG_true_ne_last _ _ _)]
  rw [h0, add_zero]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
    intro h
    apply hab
    simpa using (ePG (i + 1) (t + 1)).injective h

theorem det_uM (n : ℕ) (s : ℝ) (w : Fin n → k) : dpowM n s (uM k n w) = 1 := by
  have h : Matrix.GeneralLinearGroup.det ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1 := by
    ext
    show Matrix.det (1 + colMat k n w) = 1
    have hT : (1 + colMat k n w).BlockTriangular id := by
      intro a b hab
      have hab' : b < a := hab
      have hb : b ≠ Fin.last n := fun h => by
        rw [h] at hab'
        exact absurd hab' (not_lt.2 (Fin.le_last a))
      simp [colMat, hb, Matrix.one_apply_ne hab'.ne']
    rw [Matrix.det_of_upperTriangular hT]
    refine Finset.prod_eq_one fun a _ => ?_
    induction a using Fin.lastCases with
    | last => simp [colMat]
    | cast a => simp [colMat, Fin.castSucc_ne_last]
  show detChar (Fin (n + 1)) (absPow k ((s : ℝ) : ℂ)) ((uM k n w : Mir k n) : GL (Fin (n + 1)) k) = 1
  simp [detChar, h]

theorem mk_twist {n : ℕ} (ψ : AddChar k Circle) (τ : MRep k (n + 1)) (w : Fin (n + 1) → k) (a : τ.V) :
    (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ (τ.ρ (uM k (n + 1) w) a) =
      ((Circle.toUnits (ψ (w (Fin.last n))) : ℂˣ) : ℂ) •
        (twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n)).mkQ a := by
  have hm : uM k (n + 1) w ∈ MirUin k (n + 1) := ⟨_, rfl⟩
  have hc := mirChar_eq k ψ n ⟨uM k (n + 1) w, hm⟩ (Multiplicative.ofAdd w) rfl
  have hk : τ.ρ (uM k (n + 1) w) a - ((mirChar k ψ n ⟨uM k (n + 1) w, hm⟩ : ℂˣ) : ℂ) • a ∈
      twKer τ.ρ (MirUin k (n + 1)) (mirChar k ψ n) :=
    Submodule.subset_span ⟨⟨uM k (n + 1) w, hm⟩, a, rfl⟩
  have h := (Submodule.Quotient.mk_eq_zero _).2 hk
  rw [Submodule.Quotient.mk_sub, sub_eq_zero, Submodule.Quotient.mk_smul, hc] at h
  exact h

theorem qO_sigX {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (c : Fin (i + 1) → k)
    (z : τ.V ⊗[ℂ] σ.V) :
    qO τ σ ψ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ z) =
      ((Circle.toUnits (ψ (c (Fin.last i))) : ℂˣ) : ℂ) • qO τ σ ψ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), smul_add]
  | tmul a b =>
    have e : sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (a ⊗ₜ b) = τ.ρ (uM k (i + 1) c) a ⊗ₜ b := by
      have h1 := extTensor_tmul (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ
        (pgProj k (i + 1) (t + 1) ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) a b
      rw [pgProj_fst, pgProj_snd, map_one] at h1
      refine h1.trans ?_
      have h2 : (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (uM k (i + 1) c) a = τ.ρ (uM k (i + 1) c) a := by
        show GlobalTheory.SmGL.twist τ.ρ (dpowM (i + 1) (((t + 1 : ℕ) : ℝ) / 2)) (uM k (i + 1) c) a = _
        simp [GlobalTheory.SmGL.twist, det_uM]
      rw [h2]
      rfl
    rw [e]
    show (twKer τ.ρ (MirUin k (i + 1)) (mirChar k ψ i)).mkQ (τ.ρ (uM k (i + 1) c) a) ⊗ₜ[ℂ] b = _
    rw [mk_twist]
    exact (TensorProduct.smul_tmul' _ _ _).symm

theorem vec_split (i t : ℕ) (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k) :
    Fin.append (0 : Fin (i + 1) → k) d + Fin.append c d' =
      cVec i t c + Fin.append (0 : Fin (i + 1) → k) (d + d') := by
  funext x
  refine Fin.addCases (fun a => ?_) (fun b => ?_) x <;> simp [cVec]

theorem dEmb_eq (i t : ℕ) (d : Fin (t + 1) → k) :
    dEmb k i t d = uM k ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) := rfl

theorem mul_uM_eq (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k)
    (c : Fin (i + 1) → k) (d d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    dEmb k i t d * (wEl k i t * sEmb k _ m₀) * uM k _ v =
      uM k ((i + 1) + (t + 1)) (cVec i t c) * (dEmb k i t (d + d') * (wEl k i t * sEmb k _ m₀)) := by
  have hy : wEl k i t * sEmb k _ m₀ = levi k _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) :=
    (map_mul (levi k _) _ _).symm
  have h1 := levi_mul_uM _ (wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k)) v
  rw [hw] at h1
  rw [hy, mul_assoc, h1, dEmb_eq, dEmb_eq, ← mul_assoc, ← mul_assoc]
  congr 1
  have e1 := uM_add (k := k) ((i + 1) + (t + 1)) (Fin.append (0 : Fin (i + 1) → k) d) (Fin.append c d')
  have e2 := uM_add (k := k) ((i + 1) + (t + 1)) (cVec i t c) (Fin.append (0 : Fin (i + 1) → k) (d + d'))
  rw [vec_split] at e1
  exact e1.symm.trans e2

theorem w_coord (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v
      (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := by
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  show (Equiv.Perm.permMatrix k (piPerm i t)⁻¹).mulVec _ _ = _
  rw [Matrix.permMatrix_mulVec, ← piPerm_last]
  have h : (piPerm i t)⁻¹ (piPerm i t (Fin.last ((i + 1) + t))) = Fin.last ((i + 1) + t) := by simp
  simp only [Function.comp, h]
  exact mulVec_last_of_mem k _ m₀.2 v

theorem evX_mul {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (h : HPG k (i + 1) (t + 1))
    (p : Mir k ((i + 1) + (t + 1))) :
    evX f ((h : Mir k ((i + 1) + (t + 1))) * p) = sigX τ σ h (evX f p) :=
  (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 h p

theorem intO_translate {i t : ℕ} {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (y : Mir k ((i + 1) + t + 1)) (T : τ.V ⊗[ℂ] σ.V →ₗ[ℂ] τ.V ⊗[ℂ] σ.V) (d' : Fin (t + 1) → k)
    (F : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V) (hF : ∀ d, F d = T (evX f (dEmb k i t (d + d') * y))) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) F = T (intO f y) := by
  letI : MeasurableSpace (Fin (t + 1) → k) := borel _
  haveI : BorelSpace (Fin (t + 1) → k) := ⟨rfl⟩
  haveI : (muD k (t + 1)).IsAddHaarMeasure := by
    unfold muD
    infer_instance
  obtain ⟨hl, hc⟩ := GlobalTheory.T.locally_constant_compact_support_unipotent k i t τ σ f y
  let φ : (Fin (t + 1) → k) → τ.V ⊗[ℂ] σ.V := fun d => evX f (dEmb k i t d * y)
  have hl' : IsLocallyConstant (φ ∘ (· + d')) := hl.comp_continuous (Homeomorph.addRight d').continuous
  have hc' : HasCompactSupport (φ ∘ (· + d')) := hc.comp_homeomorph (Homeomorph.addRight d')
  have e : F = T ∘ (φ ∘ (· + d')) := funext hF
  have h2 : GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) (φ ∘ (· + d')) = GlobalTheory.CompanionTheory.Rodier.smInt (muD k (t + 1)) φ :=
    GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_comp_measurePreserving (muD k (t + 1))
      (MeasureTheory.measurePreserving_add_right (muD k (t + 1)) d') hl
  rw [e, GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear (muD k (t + 1)) T hl' hc', h2]
  rfl

theorem intO_cInd_uM_eq_sigX_intO {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) (c : Fin (i + 1) → k) (d' : Fin (t + 1) → k)
    (hw : ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v = Fin.append c d') :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀) =
      sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ (intO f (wEl k i t * sEmb k _ m₀)) := by
  refine intO_translate f _ (sigX τ σ ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩) d' _ fun d => ?_
  have e := mul_uM_eq i t m₀ v c d d' hw
  refine (congrArg (evX f) e).trans ?_
  exact evX_mul f ⟨uM k _ (cVec i t c), uM_mem_HPG i t c⟩ _

def wV (i t : ℕ) (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) : Fin ((i + 1) + (t + 1)) → k :=
  ((wGL k i t * (m₀ : GL (Fin ((i + 1) + t + 1)) k) : GL (Fin ((i + 1) + t + 1)) k) :
      Matrix (Fin ((i + 1) + t + 1)) (Fin ((i + 1) + t + 1)) k).mulVec v

theorem qO_intO_cInd {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (m₀ : Mir k ((i + 1) + t)) (v : Fin ((i + 1) + t + 1) → k) :
    qO τ σ ψ (intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) (wEl k i t * sEmb k _ m₀)) =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) •
        qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀)) := by
  have hsplit : wV i t m₀ v = Fin.append (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j))
      (fun j => wV i t m₀ v (Fin.natAdd (i + 1) j)) :=
    (Fin.append_castAdd_natAdd).symm
  have hc : wV i t m₀ v (Fin.castAdd (t + 1) (Fin.last i)) = v (Fin.last ((i + 1) + t)) := w_coord i t m₀ v
  have h1 := intO_cInd_uM_eq_sigX_intO ψ τ σ f m₀ v _ _ hsplit
  have h2 := qO_sigX ψ τ σ (fun j => wV i t m₀ v (Fin.castAdd (t + 1) j)) (intO f (wEl k i t * sEmb k _ m₀))
  refine (congrArg (qO τ σ ψ) h1).trans (h2.trans ?_)
  exact congrArg (fun x => ((Circle.toUnits (ψ x) : ℂˣ) : ℂ) • qO τ σ ψ (intO f (wEl k i t * sEmb k _ m₀))) hc

theorem eO_cInd_uM {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (uM k _ v) f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m :=
  (congrArg (fun z => ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) • z)
    (qO_intO_cInd ψ τ σ f (castM k (by omega) m) v)).trans (smul_comm _ _ _)

theorem exists_unip {n : ℕ} (u : MirUin k n) : ∃ v : Multiplicative (Fin n → k),
    unip k n v = ((u : Mir k n) : GL (Fin (n + 1)) k) := u.2

theorem eO_of_eq {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (g : Mir k ((i + 1) + (t + 1))) (v : Fin ((i + 1) + t + 1) → k) (m : Mir k (i + (t + 1)))
    (hg : g = uM k ((i + 1) + (t + 1)) v) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) m =
      ((Circle.toUnits (ψ (v (Fin.last ((i + 1) + t)))) : ℂˣ) : ℂ) • eO ψ f m := by
  subst hg
  exact eO_cInd_uM ψ τ σ f v m

theorem eO_cInd_eq_mirChar_smul {i t : ℕ} (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ) (m : Mir k (i + (t + 1))) :
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) m =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f m := by
  refine Exists.elim (exists_unip u) fun v hv => ?_
  have hu : (u : Mir k ((i + 1) + (t + 1))) = uM k ((i + 1) + (t + 1)) v.toAdd := Subtype.ext hv.symm
  have hθ := mirChar_eq k ψ ((i + 1) + t) u v hv.symm
  refine (eO_of_eq ψ τ σ f _ v.toAdd m hu).trans ?_
  exact congrArg (fun x : ℂˣ => (x : ℂ) • eO ψ f m) hθ.symm

theorem eO_cInd : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ u f
  funext m
  exact eO_cInd_eq_mirChar_smul ψ τ σ u f m

end GlobalTheory.CompanionTheory.BZPhiPG.TwO

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenEvaluationEquivariantStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_evaluation_equivariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (u : MirUin k ((i + 1) + t + 1)) (f : XS τ σ),
  eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (u : Mir k ((i + 1) + t + 1)) f) =
      ((mirChar k ψ ((i + 1) + t) u : ℂˣ) : ℂ) • eO ψ f := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | exact GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.TwO.eO_cInd <;> assumption)
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {i t : ℕ}

theorem mcast_spec {a b : ℕ} (h : a = b) (Y : MRep k a) :
    ∃ e : Y.V ≃ₗ[ℂ] (mcast h Y).V, ∀ x v, e (Y.ρ x v) = (mcast h Y).ρ (castM k h x) (e v) := by
  subst h
  exact ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem dpowM_castM {a b : ℕ} (h : a = b) (s : ℝ) (x : Mir k a) : dpowM b s (castM k h x) = dpowM a s x := by
  subst h
  rfl

theorem mExt_mcast {a b : ℕ} (h : a = b) {A B C : MRep k a} (H : MExt A B C) :
    MExt (mcast h A) (mcast h B) (mcast h C) := by
  subst h
  exact H

theorem phiN_mcast (ψ : AddChar k Circle) {a b : ℕ} (h : a = b) (h' : a + 1 = b + 1) (X : MRep k (a + 1)) :
    phiN ψ (mcast h' X) = mcast h (phiN ψ X) := by
  subst h
  rfl

theorem mcast_mcast {a b c : ℕ} (h₁ : a = b) (h₂ : b = c) (h₃ : a = c) (X : MRep k a) :
    mcast h₂ (mcast h₁ X) = mcast h₃ X := by
  subst h₁
  subst h₂
  rfl

theorem evX_cInd {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ) (g p : Mir k ((i + 1) + t + 1)) :
    evX (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) p = evX f (p * g) := rfl

theorem intC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intC ψ f (y * g) := by
  simp only [intC, evX_cInd, mul_assoc]

theorem intO_translate {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (g y : Mir k ((i + 1) + t + 1)) :
    intO (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) g f) y = intO f (y * g) := by
  simp only [intO, evX_cInd, mul_assoc]

abbrev XR (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) := prodPGn (i := i + 1) (t := t + 1) τ σ

theorem eC_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k ((i + 1) + t)) :
    eC ψ f (x * m) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eC ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) x := by
  simp only [eC, map_mul, Units.val_mul, intC_translate, smul_smul, mul_comm]

theorem eO_translate (ψ : AddChar k Circle) {τ : MRep k (i + 1)} {σ : GRep k (t + 1)} (f : XS τ σ)
    (x m : Mir k (i + (t + 1))) :
    eO ψ f (x * m) = ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) •
      eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) (castM k (by omega : i + (t + 1) = (i + 1) + t) m)) f) x := by
  simp only [eO, map_mul, Units.val_mul, intO_translate, smul_smul, mul_comm, mul_assoc]

def XR' (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t + 1) :=
  ⟨XS τ σ, cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)⟩

def RC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k ((i + 1) + t) :=
  ⟨cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ), cInd (MirabolicParabolic k (i + 1) t) (sigC τ σ)⟩

def RO (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : MRep k (i + (t + 1)) :=
  ⟨cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), cInd (HPG k i (t + 1)) (sigO τ σ ψ)⟩

set_option maxHeartbeats 1000000 in
theorem xr_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : XR τ σ = XR' τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem rc_eq (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : prodGPn (psiN τ) (gres σ) = RC τ σ := rfl

set_option maxHeartbeats 1000000 in
theorem ro_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    prodPGn (phiN ψ τ) σ = RO ψ τ σ := rfl

theorem rho_eq (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ m (Submodule.Quotient.mk f) =
      ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
        (Submodule.Quotient.mk (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) :
          TwJacquet (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ)) (MirUin k ((i + 1) + t + 1)) (mirChar k ψ ((i + 1) + t))) := rfl

def jC (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) :
    (RC τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) :=
  (indSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype ∘ₗ (smoothPart (ind (MirabolicParabolic k (i + 1) t) (sigC τ σ))).subtype ∘ₗ
    (cIndSpace (MirabolicParabolic k (i + 1) t) (sigC τ σ)).subtype

def mirabolicRestriction (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    (RO ψ τ σ).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
  (LinearMap.funLeft ℂ _ (fun m => (castM k hh).symm m)) ∘ₗ
    (indSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype ∘ₗ (smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).subtype ∘ₗ
      (cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).subtype

theorem jC_inj (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) : Function.Injective (jC τ σ) :=
  fun _ _ hab => Subtype.ext (Subtype.ext (Subtype.ext hab))

theorem jO0_inj (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hh : i + (t + 1) = (i + 1) + t) :
    Function.Injective (mirabolicRestriction ψ τ σ hh) := fun a b hab => by
  refine Subtype.ext (Subtype.ext (Subtype.ext ?_))
  funext m
  have h2 : (a : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) =
      (b : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (castM k hh m)) := congrFun hab (castM k hh m)
  rw [MulEquiv.symm_apply_apply] at h2
  exact h2

def eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) : XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (psiN τ).V ⊗[ℂ] σ.V) where
  toFun f := eC ψ f
  map_add' f g := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).1
  map_smul' c f := (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.1

def eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) :
    XS τ σ →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) where
  toFun f m := eO ψ f ((castM k hh).symm m)
  map_add' f g := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f g 0).2.2.1 _
  map_smul' c f := by
    funext m
    exact congrFun (GlobalTheory.T.evaluation_maps_linear k i t ψ hψ τ σ hτ hσ f f c).2.2.2 _

theorem eOl_apply (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (f : XS τ σ) (m : Mir k ((i + 1) + t)) :
    eOl ψ hψ τ σ hτ hσ hh f m = eO ψ f ((castM k hh).symm m) := rfl

theorem aO_eOl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (hh : i + (t + 1) = (i + 1) + t) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eOl ψ hψ τ σ hτ hσ hh f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eOl ψ hψ τ σ hτ hσ hh (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  show eO ψ f ((castM k hh).symm (x * m)) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
    eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) ((castM k hh).symm x)
  have e1 := map_mul (castM k hh).symm x m
  have e2 := eO_translate ψ f ((castM k hh).symm x) ((castM k hh).symm m)
  have e3 : castM k hh ((castM k hh).symm m) = m := MulEquiv.apply_symm_apply _ _
  have e4 : dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) = dpowM ((i + 1) + t) (-1 / 2) m := by
    have := dpowM_castM (k := k) hh (-1 / 2) ((castM k hh).symm m)
    rw [e3] at this
    exact this.symm
  have e6 := congrArg (fun g => eO ψ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) g) f)
    ((castM k hh).symm x)) e3
  have e7 : ((dpowM (i + (t + 1)) (-1 / 2) ((castM k hh).symm m) : ℂˣ) : ℂ) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) :=
    congrArg _ e4
  exact (congrArg (eO ψ f) e1).trans (e2.trans (congrArg₂ (· • ·) e7 e6))

theorem aC_eCl (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ)
    (hσ : IsSmooth σ.ρ) (m : Mir k ((i + 1) + t)) (f : XS τ σ) :
    rightReg ℂ _ _ m (eCl ψ hψ τ σ hτ hσ f) = ((dpowM ((i + 1) + t) (-1 / 2) m : ℂˣ) : ℂ) •
      eCl ψ hψ τ σ hτ hσ (cInd (HPG k (i + 1) (t + 1)) (sigX τ σ) (sEmb k ((i + 1) + t) m) f) := by
  funext x
  exact eC_translate ψ f x m

set_option maxHeartbeats 1000000 in
theorem phiPG_core (ψ : AddChar k Circle) (hψ : Continuous ψ) (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1))
    (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) :
    MExt (mcast (by omega : i + (t + 1) = (i + 1) + t) (RO ψ τ σ)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)) (RC τ σ) := by
  have hh : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨hUn, hθ, hCc, hHC, hCU, hdir⟩ := GlobalTheory.T.mirabolic_cell_structure_data k ψ hψ i t
  obtain ⟨e, he⟩ := mcast_spec hh (RO ψ τ σ)
  let jOl : (mcast hh (RO ψ τ σ)).V →ₗ[ℂ] (Mir k ((i + 1) + t) → (phiN ψ τ).V ⊗[ℂ] σ.V) :=
    mirabolicRestriction ψ τ σ hh ∘ₗ e.symm.toLinearMap
  have hjOl : Function.Injective jOl := (jO0_inj ψ τ σ hh).comp e.symm.injective
  have hes : ∀ (m : Mir k ((i + 1) + t)) v, e.symm ((mcast hh (RO ψ τ σ)).ρ m v) =
      (RO ψ τ σ).ρ ((castM k hh).symm m) (e.symm v) := by
    intro m v
    rw [LinearEquiv.symm_apply_eq, he, MulEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hjOe : ∀ m v, jOl ((mcast hh (RO ψ τ σ)).ρ m v) = rightReg ℂ _ _ m (jOl v) := by
    intro m v
    show mirabolicRestriction ψ τ σ hh (e.symm _) = _
    rw [hes]
    funext x
    show (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm x * (castM k hh).symm m) =
      (e.symm v : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ)).1.1.1 ((castM k hh).symm (x * m))
    rw [map_mul]
  exact GlobalTheory.T.twisted_jacquet_closed_open_sequence (HPG k (i + 1) (t + 1)) (sigX τ σ) (MirUin k ((i + 1) + t + 1)) hUn (mirChar k ψ ((i + 1) + t)) hθ hdir
    (sEmb k ((i + 1) + t)) (dpowM ((i + 1) + t) (-1 / 2)) (phiN ψ (n := (i + 1) + t) (XR' τ σ)).ρ (fun m f => rho_eq ψ τ σ m f)
    (Cl k i t) hCc hHC hCU
    (RC τ σ).ρ (mcast hh (RO ψ τ σ)).ρ
    (rightReg ℂ _ _) (rightReg ℂ _ _) (jC τ σ) jOl (jC_inj τ σ) hjOl (fun m v => rfl) hjOe
    (eCl ψ hψ τ σ hτ hσ) (eOl ψ hψ τ σ hτ hσ hh)
    (fun u f => GlobalTheory.T.closed_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f)
    (fun u f => by
      funext m
      exact congrFun (GlobalTheory.T.open_evaluation_equivariant k i t ψ hψ τ σ hτ hσ u f) _)
    (fun m f => aC_eCl ψ hψ τ σ hτ hσ m f)
    (fun m f => aO_eOl ψ hψ τ σ hτ hσ hh m f)
    (fun f => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.closed_evaluation_induced k i t ψ hψ τ σ hτ hσ f
      exact ⟨y, hy⟩)
    (fun f hf => by
      obtain ⟨y, hy⟩ := GlobalTheory.T.open_evaluation_induced k i t ψ hψ τ σ hτ hσ f hf
      refine ⟨e y, ?_⟩
      funext m
      have e1 : e.symm (e y) = y := e.symm_apply_apply y
      exact (congrArg (fun z => mirabolicRestriction ψ τ σ hh z m) e1).trans (congrFun hy _))
    (fun v => GlobalTheory.T.closed_evaluation_surjective k i t ψ hψ τ σ hτ hσ v)
    (fun v => by
      obtain ⟨f, hf, hy⟩ := GlobalTheory.T.open_evaluation_surjective k i t ψ hψ τ σ hτ hσ (e.symm v)
      refine ⟨f, hf, ?_⟩
      funext m
      exact congrFun hy _)
    (fun f hf => GlobalTheory.T.closed_evaluation_vanishing_on_open k i t ψ τ σ hτ hσ f hf)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_closed_cell k i t ψ hψ τ σ hτ hσ f h0 p hp)
    (fun f h0 p hp => GlobalTheory.T.average_vanishes_open_cell k i t ψ hψ τ σ hτ hσ f (by
      funext m
      have := congrFun h0 (castM k hh m)
      rw [eOl_apply, MulEquiv.symm_apply_apply] at this
      exact this) p hp)

theorem phiPG : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PhiPG k := by
  intro k _ _ _ _ ψ hψ _ i t τ σ hτ hσ
  have h0 : (i + 1) + t = i + t + 1 := by omega
  have H := mExt_mcast h0 (phiPG_core ψ hψ i t τ σ hτ hσ)
  rw [mcast_mcast _ _ (by omega : i + (t + 1) = i + t + 1), ← ro_eq, ← xr_eq, ← rc_eq] at H
  rw [phiN_mcast ψ h0 (by omega)]
  exact H

end GlobalTheory.CompanionTheory.BZPhiPG

end
