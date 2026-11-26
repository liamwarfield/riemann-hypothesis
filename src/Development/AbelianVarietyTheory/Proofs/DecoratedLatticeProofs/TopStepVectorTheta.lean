module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualFrameVacuumStep
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacedBesselPairCentral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistLevelStabiliserAtLevelPrimeProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorTheta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopConv

variable {D : D7}

theorem exists_finComb_of_mem_span (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {f g : WO S T → ℂ}
    (hg : g ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f)) :
    ∃ b : WO S T →₀ ℂ, IsFinComb b ∧ comb ψ S T b f = g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Finsupp.single a.1 1, fun u hu => ?_, by rw [GlobalTheory.StepComb.comb_single', one_smul]⟩
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hu)]
    exact a.2
  | zero => exact ⟨0, fun u hu => absurd hu (Finsupp.notMem_support_iff.2 rfl), GlobalTheory.StepComb.comb_zero' ψ f⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨b', hb', rfl⟩ := hy
    exact ⟨b + b', fun u hu => (Finset.mem_union.1 (Finsupp.support_add hu)).elim (hb u) (hb' u),
      GlobalTheory.StepComb.comb_add' ψ b b' f⟩
  | smul a x _ hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    exact ⟨a • b, fun u hu => hb u (Finsupp.support_smul hu), GlobalTheory.StepComb.comb_smul' ψ a b f⟩

theorem isFinComb_comp (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b b' : WO S T →₀ ℂ} (hb : IsFinComb b)
    (hb' : IsFinComb b') : ∃ c : WO S T →₀ ℂ, IsFinComb c ∧ ∀ f, comb ψ S T c f = comb ψ S T b (comb ψ S T b' f) := by
  obtain ⟨c, h1, h2⟩ := (GlobalTheory.HeisComb.main D ψ S T).1 b b'
  refine ⟨c, fun w hw => ?_, h2⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := h1 w hw
  ext i j
  have e1 := congrFun (congrFun (hb x hx) i) j
  have e2 := congrFun (congrFun (hb' y hy) i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at e1 e2 ⊢
  rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e2, add_zero]

end GlobalTheory.TopConv

end

noncomputable section

namespace GlobalTheory.TopConv

theorem comb_mem_span {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {b : WO S T →₀ ℂ} (hb : IsFinComb b)
    (f : WO S T → ℂ) :
    comb ψ S T b f ∈ Submodule.span ℂ (Set.range fun a : {a : WO S T // a.map (infPart D) = 0} => heisO ψ S T a f) := by
  unfold comb
  exact Submodule.sum_mem _ fun u hu => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hb u hu⟩, rfl⟩)


end GlobalTheory.TopConv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryPsiValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 2000000

noncomputable section

namespace GlobalTheory.FamTraceChiColChar

open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil

theorem chr_unif_congr {k : Type} [Field k] [ValuativeRel k] {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {t : kˣ} (ht : IsUnif t)
    {p y : k} (hp : valuation k ((t : k) - p) < valuation k (t : k)) (hy : valuation k y ≤ 1) :
    ψ (((t⁻¹ : kˣ) : k) * y) = ψ (p⁻¹ * y) := by
  have tp : 0 < valuation k (t : k) := zero_lt_iff.2 ((map_ne_zero _).2 t.ne_zero)
  have hpv : valuation k p = valuation k (t : k) := by
    refine Valuation.map_eq_of_sub_lt _ ?_
    rwa [Valuation.map_sub_swap]
  have p0 : p ≠ 0 := fun e => by
    rw [e, map_zero] at hpv
    exact tp.ne hpv
  have h1 : valuation k (((t : k) - p) * (t : k)⁻¹) ≤ valuation k (t : k) := (ht _).1 (by
    rw [map_mul, map_inv₀, mul_inv_lt_iff₀ tp, one_mul]
    exact hp)
  have triv : ψ (((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y) = 1 := (hψ 1).2 (by simp) _ (by
    rw [map_one, map_mul, map_mul _ _ p⁻¹, map_inv₀, hpv]
    refine mul_le_one' ?_ hy
    rw [mul_inv_le_iff₀ tp, one_mul]
    exact h1)
  have e : p⁻¹ * y = ((t⁻¹ : kˣ) : k) * y + ((t : k) - p) * (t : k)⁻¹ * p⁻¹ * y := by
    have := t.ne_zero
    rw [Units.val_inv_eq_inv_val]
    field_simp
    ring
  rw [e, AddChar.map_add_eq_mul, triv, mul_one]

theorem weil_unif_eq_exp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP) {ψ : AddChar k Circle}
    (hψ : HasConductor ψ 1) {Ψ : AddChar (AF D.host.F) ℂ} (hΨ : IsStdChar D Ψ (-1)) (hc : (ofSplit q).IsChar Ψ ψ)
    {p : ℕ} (hp : p.Prime) (hN : Ideal.absNorm PP.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2)
    {t : kˣ} (ht : IsUnif t) (htp : valuation k ((t : k) - (p : k)) < valuation k (t : k))
    {s : 𝓞 D.host.E} (hs : D.host.xi0 * (s : D.host.E) = 1) {z : 𝓞 D.host.E} {b : ℤ} (hz : z - s * b ∈ PP.asIdeal) :
    (ψ (((t⁻¹ : kˣ) : k) * (ofSplit q).pr (z : D.host.E)) : ℂ) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  obtain ⟨hv, hi, -⟩ := place_facts q h
  have h1 : valuation k (prO q z - prO q (s * b)) < 1 := by
    rw [← map_sub, ← prO_lt q h]
    exact hz
  rw [← prO_apply, GlobalTheory.LevelUnif.chr_near hψ ht h1, chr_unif_congr hψ ht htp (prO_le q h _), hc,
    ← GlobalTheory.SplitDegOneChar.psiE_sec_pr_eq_exp D k q PP p hp hN hsq hv hi Ψ hΨ ((b : D.host.E) / (p : D.host.E)) b
      (by rw [sub_self]; exact ⟨0, 1, (Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top, by simp⟩)]
  have e1 : ((p : k))⁻¹ * prO q (s * b) = q.pr (incA D ((s : D.host.E) * ((b : D.host.E) / (p : D.host.E)))) := by
    change _ = (q.pr.comp (incA D)) _
    rw [map_mul, map_mul, map_div₀, map_intCast, map_intCast, map_natCast]
    change _ = prO q s * _
    ring
  rw [e1]
  change psiE Ψ (incA D D.host.xi0 * q.sec (q.pr _)) = psiE Ψ (q.sec (q.pr (incA D _)))
  rw [q.sec_pr, q.sec_pr, mul_left_comm, ← map_mul, ← mul_assoc D.host.xi0, hs, one_mul]

theorem columnCharacter_reduction_eq_exp {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} (I : TC B X) (hI : I.Ok)
    (G : Formalism.L2.Forms.GLoc B.host.F B.host.E B.sp.cm.sig B.host.g) (hG : G.piG = X.piG)
    (hpsi : ∀ j v h (w : {w // w ∈ (B.primes X).vGs}), w.1.under (𝓞 B.host.F) = v → ∀ n : ℕ,
      G.psi0 j v h (n : Formalism.L2.Forms.kv B.host.F v) = B.embLL (I.Ch.psi0 w (n : 𝓞 B.fields.E ⧸ w.1.asIdeal)))
    (P : HeightOneSpectrum (𝓞 B.host.E)) (hPP : P ∈ (B.primes X).vGs) (j : Fin 2)
    (h : (B.host.g j : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal) (z : 𝓞 B.host.E)
    (w : (P.under (𝓞 B.host.F)).adicCompletionIntegers B.host.F)
    (hw : (w : (P.under (𝓞 B.host.F)).adicCompletion B.host.F) =
      G.phi j _ h ((z : B.host.E) ⊗ₜ[B.host.F] (1 : (P.under (𝓞 B.host.F)).adicCompletion B.host.F)))
    {s : 𝓞 B.host.E} (hs : B.host.xi0 * (s : B.host.E) = 1) (hsP : s ∉ P.asIdeal) :
    (Formalism.L2.Col.qOf P).Prime ∧ ∃ b : ℤ, z - s * b ∈ P.asIdeal ∧ G.psi0 j _ h (IsLocalRing.residue _ w) =
      Complex.exp (2 * Real.pi * Complex.I * b / ((Formalism.L2.Col.qOf P : ℕ) : ℂ)) := by
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨P', hP, ρ, hPu, hres⟩ := TC.GLev0.exists_w (X := X) G hG j _ h
  have hwP : P' = P := TC.GLev0.vGs_inj (X := X) hPP (TC.GLev0.mem_vGs.2 ⟨j, hP⟩) hPu
  subst hwP
  have hq : Formalism.L2.Col.qOf P' = B.host.g j := hPr.vG_norm j _ hP
  refine ⟨by rw [hq]; exact hPr.g_prime j, ?_⟩
  obtain ⟨n, hn⟩ := TC.GLev0.exists_natCast (X := X) hPP (Ideal.Quotient.mk _ z)
  obtain ⟨b, hb⟩ := TC.GLev0.exists_natCast (X := X) hPP (Formalism.L2.Col.redP P' B.host.xi0 * n)
  have hred := Formalism.L2.Col.reduction_spec P' (a := B.host.xi0) (r := 1) hsP (by rw [map_one, mul_comm]; exact hs)
  refine ⟨b, ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, map_mul, Int.cast_natCast, map_natCast, hb, ← mul_assoc, hred, map_one, one_mul, hn]
  obtain ⟨hh, e⟩ := hres (Formalism.UG.inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (z : B.host.E)) (Ideal.Quotient.mk _ z)
    (by rw [adAt_inclE]; exact hasRes_coe _ z)
  have ew : w = ⟨_, hh⟩ := Subtype.ext hw
  have e2 : IsLocalRing.residue _ w = (n : Formalism.L2.Forms.kv B.host.F _) := by
    rw [ew]
    exact e.trans ((congrArg ρ hn.symm).trans (map_natCast ρ n))
  have e3 := hpsi j _ h ⟨_, hPP⟩ rfl n
  have e4 := hI.weil ⟨_, hPP⟩ (n : _) (b : ℤ) ((hb.symm).trans (Int.cast_natCast b).symm)
  rw [e2]
  exact e3.trans e4

end GlobalTheory.FamTraceChiColChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevSIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.moved_mat {k Z : Type} [Field k] [Fintype Z] [DecidableEq Z] {n : ℕ} (β : Matrix (Fin n) Z k) (γ : Matrix Z (Fin n) k) (hγβ : γ * β = 1) (x : Matrix Z Z k) (e : Z ≃ Fin n) : β * x * γ * β.submatrix id e.symm = β.submatrix id e.symm * x.submatrix e.symm e.symm := by
  rw [Matrix.submatrix_mul_equiv β x id e.symm e.symm, Matrix.mul_assoc (β * x)]
  have h1 : γ * β.submatrix id e.symm = (γ * β).submatrix id e.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hγβ]
  ext i j; simp [Matrix.mul_apply, Matrix.one_apply]

theorem GlobalTheory.TopLevQ.suppAt_conj {D : D7} {e : AE D} {V : HSp D} (g b : GA D V) (hg : Formalism.L2.Theta.SuppAt e V g) :
    Formalism.L2.Theta.SuppAt e V (b⁻¹ * g * b) := by
  have hm : ∀ x y : GA D V, Formalism.L2.Theta.mt V (x * y) = Formalism.L2.Theta.mt V x * Formalism.L2.Theta.mt V y := fun x y => by
    unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl
  have h1 : Formalism.L2.Theta.mt V b⁻¹ * Formalism.L2.Theta.mt V b = 1 := by
    rw [← hm, inv_mul_cancel]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
  have key : Formalism.L2.Theta.mt V (b⁻¹ * g * b) - 1 =
      Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b := by
    rw [hm, hm, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]
  have hg' : (e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1) = Formalism.L2.Theta.mt V g - 1 := by
    ext i j; exact hg i j
  have h2 : (e + (cA D) e) • (Formalism.L2.Theta.mt V b⁻¹ * (Formalism.L2.Theta.mt V g - 1) * Formalism.L2.Theta.mt V b) =
      Formalism.L2.Theta.mt V b⁻¹ * ((e + (cA D) e) • (Formalism.L2.Theta.mt V g - 1)) * Formalism.L2.Theta.mt V b := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [hg'] at h2
  intro i j
  rw [key]
  exact congrFun (congrFun h2 i) j

theorem GlobalTheory.TopLevQ.blk_iff {K : Type} [Field K] [ValuativeRel K] {κ τ s n : ℕ}
    (e : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin n) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e)
    (x : Matrix (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) (GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2)) K) :
    (∀ i j : Fin n, Formalism.L2.DIV.blk2 (κ + (s + 1)) j < Formalism.L2.DIV.blk2 (κ + (s + 1)) i →
      ValuativeRel.valuation K (x (e.symm i) (e.symm j)) < 1) ↔ GlobalTheory.StepData.MaxM x.toBlocks₂₁ := by
  have hlo : ∀ a : Fin κ ⊕ Fin (s + 1), (e (Sum.inl a)).val < κ + (s + 1) := by
    intro a; rw [he]; rcases a with a | a <;> simp [GlobalTheory.SymBridge.zPos] <;> omega
  have hhi : ∀ p : Fin (s + 2) × Fin τ, κ + (s + 1) ≤ (e (Sum.inr p)).val := by
    intro p; rw [he]; simp only [GlobalTheory.SymBridge.zPos]; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  constructor
  · intro h p a
    have := h (e (Sum.inr p)) (e (Sum.inl a)) (by
      simp only [Formalism.L2.DIV.blk2, if_pos (hlo a), if_neg (Nat.not_lt.2 (hhi p))]; omega)
    simp only [Equiv.symm_apply_apply] at this
    exact this
  · intro h i j hij
    have hj : j.val < κ + (s + 1) := by
      by_contra hc
      simp only [Formalism.L2.DIV.blk2, if_neg hc] at hij
      split_ifs at hij <;> omega
    have hi : ¬ i.val < κ + (s + 1) := by
      intro hc
      simp only [Formalism.L2.DIV.blk2, if_pos hc, if_pos hj] at hij
      omega
    obtain ⟨p, hp⟩ : ∃ p, e.symm i = Sum.inr p := by
      rcases hi' : e.symm i with a | p
      · exfalso; apply hi; have := hlo a; rw [← hi', Equiv.apply_symm_apply] at this; exact this
      · exact ⟨p, rfl⟩
    obtain ⟨a, ha⟩ : ∃ a, e.symm j = Sum.inl a := by
      rcases hj' : e.symm j with a | p
      · exact ⟨a, rfl⟩
      · exfalso; have := hhi p; rw [← hj', Equiv.apply_symm_apply] at this; omega
    rw [hp, ha]
    exact h p a

theorem GlobalTheory.TopLevQ.mem_levS_iff {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (y : GA D V) :
    y ∈ levS V β L ↔ y ∈ GfC V ∧ ((Lev.finE V y ∈ Formalism.L2.DIV.St β ∧
        (∀ PP' ∈ L.Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf L.r L.t)) ∧
        ∀ PP' ∈ L.Q, Formalism.L2.DIV.redFn β PP' (Lev.finE V y) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 L.r)) ∧
        Formalism.L2.DIV.rTup β L (Lev.finE V y) ∈ L.P.H) := by
  show y ∈ GfC V ⊓ Subgroup.comap (Lev.finE V) (Formalism.L2.DIV.lev _ _ β L) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap]
  show _ ∧ (_ ∈ Formalism.L2.DIV.parLev _ _ _ _ ∧ _) ↔ _
  rw [Formalism.L2.DIV.mem_parLev]
  simp only [GlobalTheory.LevSplit.finE_mem_UA, true_and]

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.TopLevQ.red_eq_zero_iff : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (t h : GA D V) (N M : Matrix (Fin V.rank) (Fin V.rank) k), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) V t β N → (Formalism.L2.Theta.mt V h).map q.pr * N = N * M → Lev.finE V (t⁻¹ * h * t) ∈ Formalism.L2.DIV.St β → ∀ i j, ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j = 0 ↔ ValuativeRel.valuation k (M i j) < 1) := by
  intro D k _ _ _ _ q PP hPP V β t h N M hN hM hSt i j
  constructor
  · intro h0
    have := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j 0 (by rw [h0, map_zero])
    have e0 : (GlobalTheory.LocMod.ofSplit q).pr ((0 : 𝓞 D.host.E) : D.host.E) = 0 := by
      show (GlobalTheory.LocMod.ofSplit q).π ((incA D) ((0 : 𝓞 D.host.E) : D.host.E)) = 0
      rw [show ((0 : 𝓞 D.host.E) : D.host.E) = 0 from rfl, map_zero, map_zero]
    rwa [e0, sub_zero] at this
  · intro hv
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective ((Formalism.L2.DIV.redFn β PP (Lev.finE V (t⁻¹ * h * t))).val i j)
    have h1 := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β t h N M hN hM hSt i j z hz
    have h2 : ValuativeRel.valuation k ((GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) < 1 := by
      have e : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = M i j - (M i j - (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E)) := by ring
      rw [e]
      exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
    obtain ⟨π', hπ, hred, -⟩ := GlobalTheory.T.exists_finiteAdele_projection_integral_reduction D k q PP hPP
    have h6 : (GlobalTheory.LocMod.ofSplit q).pr (z : D.host.E) = (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) := (hπ _).symm
    rw [h6, ← hred.ker, Formalism.L2.DIV.resS_oToS] at h2
    rw [← hz, h2]


end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlaceFrameExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplit
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.LineIdeal

open GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem exists_dominant {k : ℕ} (f : Fin k → Fv F v) (hf : ∃ j, f j ≠ 0) :
    ∃ j, f j ≠ 0 ∧ ∀ c : Fv F v,
      (∀ i, c * f i ∈ v.adicCompletionIntegers F) ↔ c * f j ∈ v.adicCompletionIntegers F := by
  obtain ⟨j0, hj0⟩ := hf
  haveI : Nonempty (Fin k) := ⟨j0⟩
  obtain ⟨j, hj⟩ := Finite.exists_max fun i => ‖f i‖₊
  refine ⟨j, fun h0 => hj0 ?_, fun c => ⟨fun h => h j, fun h i => ?_⟩⟩
  · have := hj j0
    rw [h0, nnnorm_zero] at this
    exact nnnorm_eq_zero.1 (le_antisymm this zero_le)
  · rw [← nnnorm_le_one_iff_mem] at h ⊢
    rw [nnnorm_mul] at h ⊢
    exact (mul_le_mul_of_nonneg_left (hj i) zero_le).trans h

theorem exists_unit_gen (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {k : ℕ} {u l : Fin k → Fv F v ⊗[F] E}
    (hl : ∑ j, l j * u j = 1) :
    ∃ α : (Fv F v ⊗[F] E)ˣ, ∀ c : Fv F v ⊗[F] E,
      (∀ j, c * u j ∈ intLoc F E v) ↔ ((α⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) * c ∈ intLoc F E v := by
  have hne : ∀ ρ : E →ₐ[F] Fv F v, ∃ j, splitProj ρ (u j) ≠ 0 := fun ρ => by
    by_contra hc
    push_neg at hc
    have := congrArg (splitProj ρ) hl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one, Finset.sum_eq_zero fun j _ => by rw [map_mul, hc j, mul_zero]] at this
    exact zero_ne_one this
  obtain ⟨j1, h1, hj1⟩ := exists_dominant (fun j => splitProj τ (u j)) (hne τ)
  obtain ⟨j2, h2, hj2⟩ := exists_dominant (fun j => splitProj (τ.comp σ) (u j)) (hne _)
  beta_reduce at h1 h2 hj1 hj2
  refine ⟨⟨(splitAlgEquiv h τ).symm ((splitProj τ (u j1))⁻¹, (splitProj (τ.comp σ) (u j2))⁻¹),
    (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)), ?_, ?_⟩, fun c => ?_⟩
  · rw [← map_mul, Prod.mk_mul_mk, inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    exact map_one _
  · rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel₀ h1, mul_inv_cancel₀ h2]
    exact map_one _
  · show _ ↔ (splitAlgEquiv h τ).symm (splitProj τ (u j1), splitProj (τ.comp σ) (u j2)) * c ∈ intLoc F E v
    simp only [mem_intLoc_iff_split h τ, map_mul, splitProj_symm, splitProj_comp_symm, forall_and]
    rw [hj1 (splitProj τ c), hj2 (splitProj (τ.comp σ) c), mul_comm (splitProj τ c),
      mul_comm (splitProj (τ.comp σ) c)]

end Local


set_option maxHeartbeats 1600000 in
theorem exists_unit_mult_latLoc : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsFullLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  intro D v hτ n L hL g ε hε
  obtain ⟨τ⟩ := hτ
  obtain ⟨k, S, Φ, h1, hS, hΦ⟩ := SelfDual.exists_frame L hL
  have h2 := SelfDual.map_mul_eq_one (F := D.host.F) (Fv D.host.F v) h1
  let w : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E := g.val *ᵥ fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i
  obtain ⟨l, hl⟩ : ∃ l : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E, l ⬝ᵥ w = 1 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hε
    refine ⟨Pi.single i ((1 : Fv D.host.F v) ⊗ₜ[D.host.F] (ε i)⁻¹) ᵥ* (g⁻¹ : GL (Fin n) _).val, ?_⟩
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, single_dotProduct,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (by simpa using hi)]
    rfl
  let u := Φ.map (inclR (F := D.host.F) (Fv D.host.F v)) *ᵥ w
  have hl' : ∑ j, (l ᵥ* S.map (inclR (F := D.host.F) (Fv D.host.F v))) j * u j = 1 := by
    change (l ᵥ* _) ⬝ᵥ u = 1
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, hl]
  have key : ∀ a : Fv D.host.F v ⊗[D.host.F] D.host.E,
      a • w ∈ latLoc D.host.F L v ↔ ∀ j, a * u j ∈ intLoc D.host.F D.host.E v := fun a => by
    rw [SelfDual.mem_latLoc_iff_of_frame h1 hS hΦ v, Matrix.mulVec_smul]
    rfl
  obtain ⟨α, hα⟩ := exists_unit_gen (isCMExt_host D) τ hl'
  refine ⟨α, fun c => ?_⟩
  have hcw : g.val *ᵥ (c • fun i => (1 : Fv D.host.F v) ⊗ₜ[D.host.F] ε i) = c • w := Matrix.mulVec_smul _ _ _
  rw [hcw, key, hα]

end GlobalTheory.LineIdeal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitMultipliersLineInMovedLatticeSplitStatement
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_multipliers_line_in_movedLattice_split : ∀ (D : D7) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F)), Nonempty (D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) → ∀ (n : ℕ) (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), Submodule.IsFullLattice D.host.E L → ∀ (g : GL (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) (ε : Fin n → D.host.E), ε ≠ 0 → ∃ α : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ, ∀ c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, Matrix.mulVec g.val (c • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v ↔ ((α⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E) * c ∈ GlobalTheory.AdelicU.intLoc D.host.F D.host.E v := by
  first | exact @GlobalTheory.LineIdeal.exists_unit_mult_latLoc | exact GlobalTheory.LineIdeal.exists_unit_mult_latLoc | (intros; apply GlobalTheory.LineIdeal.exists_unit_mult_latLoc <;> first | assumption | (letI := ‹Submodule.IsFullLattice _ _›; infer_instance))
end
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
noncomputable section

namespace GlobalTheory.LineAtG


set_option maxHeartbeats 1600000 in
theorem mem_latLoc_line_iff {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (L : GlobalTheory.FinPl.Lat V) (hL : L.FG) (v : GlobalTheory.FinPl.Pl D) (t : GA D V)
    (ε : Fin V.rank → D.host.E) (y : AE D) (hy : y ∈ GlobalTheory.FinPl.idAt D (· = v)) :
    Matrix.mulVec ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram
        (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v t))⁻¹).val
        (GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i) ∈
        GlobalTheory.AdelicU.latLoc D.host.F L v ↔
      Matrix.mulVec (Formalism.L2.Theta.mt V t⁻¹) (fun i => y * Formalism.L2.Theta.incA D (ε i)) ∈ GlobalTheory.FinPl.latV V L (· = v) := by
  have hy' : ∀ i, (fun i => y * Formalism.L2.Theta.incA D (ε i)) i ∈ GlobalTheory.FinPl.idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ hy
  rw [GlobalTheory.StMoves.mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ t⁻¹ hy'), GlobalTheory.FinPl.KOpen.fin_mulVec,
    GlobalTheory.AdelicU.vecLoc_mulVec, map_inv, map_inv]
  have hv : GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun i => y * Formalism.L2.Theta.incA D (ε i)) =
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ fun _ : Fin 1 => y) 0 • fun i => (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) ⊗ₜ[D.host.F] ε i := by
    funext i
    simp only [Function.comp, GlobalTheory.AdelicU.vecLoc, Pi.smul_apply, smul_eq_mul, map_mul]
    congr 1
  rw [hv]


end GlobalTheory.LineAtG
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIffCharacterTrivialSplit
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitIntChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem triv_of_le_one {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {y : k} (hy : valuation k y ≤ 1) : ψk y = 1 :=
  (hc 1).2 (by simp) y (by simpa using hy)

theorem trivial_iff_mem {ψk : AddChar k Circle} (hc : HasConductor ψk 1) {ξ : k} (hξ : valuation k ξ = 1) (t : k) :
    (∀ c ∈ 𝒪[k], ψk (t * c / ξ) = 1) ↔ t ∈ 𝒪[k] := by
  have hξ0 : ξ ≠ 0 := fun h => by simp [h] at hξ
  constructor
  · intro h
    by_cases ht : t = 0
    · rw [ht]; exact zero_mem _
    have h1 := (hc (t / ξ)).1 (fun y hy => by
      have hc' : y * ξ / t ∈ 𝒪[k] := by
        rw [Valuation.mem_integer_iff, map_div₀, map_mul, hξ, mul_one]
        rw [map_div₀, hξ, div_one] at hy
        exact div_le_one_of_le₀ hy zero_le'
      have := h _ hc'
      rwa [show t * (y * ξ / t) / ξ = y by field_simp] at this)
    rw [Valuation.mem_integer_iff]
    simpa [map_div₀, hξ] using h1
  · intro ht c hc'
    apply triv_of_le_one hc
    rw [map_div₀, hξ, div_one]
    exact (Valuation.mem_integer_iff _ _).1 (mul_mem ht hc')

theorem int_iff_psiE : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), valuation k ((ofSplit q).xi) = 1 → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ s ∈ GlobalTheory.FinPl.idAt D (· = q.v), (s ∈ GlobalTheory.FinPl.intAt D (· = q.v) ↔ ∀ o ∈ GlobalTheory.FinPl.intAt D (· = q.v), psiE ψ (s * o) = 1) := by
  intro D k _ _ _ _ q ψ ψk hξ hχ hc s hs
  have hι : ∀ y, psiE ψ (q.sec y) = ψk (y / (ofSplit q).xi) := fun y => GlobalTheory.LocBesChar.psiE_ι (ofSplit q) hχ y
  have hone : ∀ y, valuation k y ≤ 1 → psiE ψ (q.sec y) = 1 := fun y hy => by
    rw [hι, triv_of_le_one hc (by rw [map_div₀, hξ, div_one]; exact hy)]; rfl
  constructor
  · intro hsI o ho
    have hso : s * o ∈ GlobalTheory.FinPl.idAt D (· = q.v) := Ideal.mul_mem_right _ _ hs
    obtain ⟨h1, h2⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q hs).1 hsI
    obtain ⟨h3, h4⟩ := (GlobalTheory.SplitIntComp.mem_intAt_iff q ho.1).1 ho
    rw [GlobalTheory.SplitIntComp.eq_sec_add_csec q hso, psiE_add, GlobalTheory.LocBesChar.psiE_cA, hone, hone, one_mul]
    · rw [map_mul, map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h2 h4)
    · rw [map_mul]; exact (Valuation.mem_integer_iff _ _).1 (mul_mem h1 h3)
  · intro h
    rw [GlobalTheory.SplitIntComp.mem_intAt_iff q hs]
    constructor
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : q.sec c ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.FinPl.FrameLat.sec_mul_right, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)
    · rw [← trivial_iff_mem hc hξ]
      intro c hc'
      have hm : cA D (q.sec c) ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
        simpa using (GlobalTheory.Core.Mi.LatMatch.mul_cA_sec_mem_intAt_iff q 1 c).2 (by simpa using hc')
      have := h _ hm
      rw [mul_comm, GlobalTheory.Core.Mi.LatMatch.cA_sec_mul, GlobalTheory.LocBesChar.psiE_cA, hι, mul_comm c] at this
      exact Circle.coe_inj.1 (this.trans Circle.coe_one.symm)

end GlobalTheory.SplitIntChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslateSumEqZeroOfChartRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslateSumEqZeroOfChartRepresentatives
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaReduce

theorem conj_level {G ι : Type*} [Group G] (U : Subgroup G) (χ : U →* ℂˣ) (J : List ι) (f : ι → G) (x κ' : G) (κ : U)
    (hκ : κ.1 = (J.map f).prod * κ') (hc : x * κ' = κ' * x)
    (h1 : ∀ i, ∃ h : f i ∈ U, χ ⟨_, h⟩ = 1) (h2 : ∀ i, ∃ h : x⁻¹ * f i * x ∈ U, χ ⟨_, h⟩ = 1) :
    ∃ κ'' : U, κ.1 * x = x * κ''.1 ∧ χ κ'' = χ κ := by
  let K : Subgroup G := χ.ker.map U.subtype
  have hK : ∀ g, (∃ h : g ∈ U, χ ⟨_, h⟩ = 1) → g ∈ K := fun g ⟨h, h'⟩ => ⟨⟨g, h⟩, h', rfl⟩
  have hP : (J.map f).prod ∈ K := K.list_prod_mem fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact hK _ (h1 i)
  have hP' : (J.map f).prod ∈ K.comap (MulAut.conj x⁻¹).toMonoidHom := Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    have := hK _ (h2 i)
    simpa using this
  have hP'' : x⁻¹ * (J.map f).prod * x ∈ K := by simpa using hP'
  obtain ⟨m, hm, hm'⟩ := K.mul_mem hP'' (K.inv_mem hP)
  have hm1 : χ m = 1 := hm
  have hm2 : m.1 = x⁻¹ * (J.map f).prod * x * (J.map f).prod⁻¹ := hm'
  refine ⟨m * κ, ?_, by rw [map_mul, hm1, one_mul]⟩
  rw [Subgroup.coe_mul, hm2, hκ, mul_assoc, ← hc]
  group

variable {D : D7}

theorem real_le_off (V : HSp D) (P : Pl D → Prop) : GinfC V ≤ grpOff V P := by
  intro a ha
  rw [GinfC, MonoidHom.mem_ker] at ha
  rw [grpOff, GlobalTheory.FinPl.LocProd.mem_congGrp_entries]
  intro i j
  have h2 : finPart D (Formalism.L2.Theta.mt V a i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun x : GL (Fin V.rank) _ => x.1 i j) ha
  rw [idOff, Ideal.mem_iInf]
  intro w
  rw [RingHom.mem_ker, Matrix.sub_apply, GlobalTheory.FinPl.compAt, RingHom.comp_apply, RingHom.map_sub, h2]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one, sub_self, RingHom.map_zero]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero, sub_self, RingHom.map_zero]

theorem grpOff_anti (V : HSp D) {P P' : Pl D → Prop} (h : ∀ w, P' w → P w) : grpOff V P ≤ grpOff V P' := by
  apply GlobalTheory.FinPl.LocProd.congGrp_mono
  intro a ha
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall] at ha ⊢
  exact fun w hw => ha w (h w hw)

end GlobalTheory.AdForm.DiaReduce


open GlobalTheory.AdForm.DiaReduce in
theorem GlobalTheory.AdForm.DiaReduce.rd_laws {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hpins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch) (hA : A.Is)
    (θ : InfFam (I.rec7 l Z)) (hθ : IsInfFam θ) (i : ℕ) (hi : i ≤ B.R.m) (φ) (hφ : φ ∈ (I.fm l u a).Fi i) (β : Ch i)
    (y : (I.chain l u a).Y i) (k : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (hk : k ∈ GinfC ((I.rec7 l Z).sp.X i)) :
    ∃ y' : (I.chain l u a).Y i, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ g, ∀ κ : A.U i β,
      A.rd θ i hi β φ y (γ * (g * k * κ.1)) = (A.chi i β κ : ℂ) * A.rd θ i hi β φ y' g := by
  let eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi :=
    { toFun := fun y => ⟨y.1, y.2⟩, invFun := fun z => ⟨z.1, z.2⟩, left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hV := GlobalTheory.Mem.Col2.TC.val_tied I hok hpins l Z u a i hi (A.bad i) (Ch i) (A.chOf i) (A.K i hi) eY
    ⟨A.kb i, hA.reads i hi⟩ (fun _ => rfl)
  have hF := (hV.Fi φ).1 hφ
  have laws := GlobalTheory.AdForm.RdLaw.rdS_laws (I.rec7 l Z) θ hθ ((I.rec7 l Z).sp.X i) (B.R.N i) (rankN (I.rec7 l Z) i hi)
    (gramN (I.rec7 l Z) i hi) rfl (B.T u) (I.rec7 l Z).R.f (A.bad i) (A.K i hi β).lev {c // A.chOf i c = β}
    (A.K i hi β).y (A.K i hi β).y_bij _ (fun c z => φ c.1 ⟨z.1, z.2⟩) (hF β) ⟨y.1, y.2⟩
  obtain ⟨hL, hK, hR, -⟩ := laws
  let z := GlobalTheory.AdForm.Model.trFr θ ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) k (eY y)
  refine ⟨eY.symm z, fun γ hγ g κ => ?_⟩
  obtain ⟨hκf, κ', hκ'⟩ := (hA.U i hi β κ.1).1 κ.2
  have hchi := hA.chi i hi β κ κ' hκ'
  have e1 := hL γ hγ (g * k * κ.1)
  have e2 := hK κ.1 hκf κ' hκ' (g * k)
  have e3 := hR k hk z (fun τ => rfl) g
  exact e1.trans (e2.trans (congrArg₂ (· * ·) (congrArg (fun x : ℂˣ => (x : ℂ)) hchi.symm) e3))


open GlobalTheory.AdForm.DiaReduce in
theorem GlobalTheory.AdForm.diaSum_eq_zero_of_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y, (∀ (c : {c // A.chOf j c = b}) y', ∑ᶠ s, A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) = 0) → ∀ x, ∑ᶠ s, A.rd θ j hj b φ y (x * (β j i).gl (g s)) = 0 := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v _ g hg b y h0 x
  have hinj := GlobalTheory.AdForm.StdT.places_injective I hok hpins l Z u p β Q L hS
  obtain ⟨e, -⟩ := hS.1
  haveI : Finite ι := Finite.of_equiv _ e.symm
  haveI : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hst, hdec⟩ := GlobalTheory.T.twistLevelStabiliserAtLevelPrime_proof I hok hpins l Z u a Ch A hA k ι p β Q L hS (Finset.univ.toList) (Finset.nodup_toList _)
    (fun i => Finset.mem_toList.2 (Finset.mem_univ i)) j hj b
  obtain ⟨γ, hγ, c, r, hr, κ, hκ, rfl⟩ := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hok hpins l Z u a Ch A hA j hj b).1.dec x
  obtain ⟨g', hg', κ', hκ', hκe⟩ := hdec κ hκ
  obtain ⟨y', hy'⟩ := rd_laws I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b y r hr
  have hAt : ∀ i' t, (β j i').gl t ∈ grpAt ((I.rec7 l Z).sp.X j) (· = (p i').v) := fun i' t =>
    GlobalTheory.FinPl.FrameLat.gl_mem_grpAt (β j i') t
  have hcomm := ((GlobalTheory.FinPl.localComponents (I.rec7 l Z) (· = (p i).v)).2 ((I.rec7 l Z).sp.X j)).2.1
  have key : ∀ s, A.rd θ j hj b φ y (γ * (A.h j b c * r) * κ * (β j i).gl (g s)) =
      (A.chi j b ⟨κ, hκ⟩ : ℂ) * A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) := by
    intro s
    obtain ⟨κ'', h1, h2⟩ := conj_level (A.U j b) (A.chi j b) Finset.univ.toList (fun i' => (β j i').gl (g' i'))
      ((β j i).gl (g s)) κ' ⟨κ, hκ⟩ hκe
      (hcomm _ (hAt i _) _ (grpOff_anti _ (fun w hw => ⟨i, hw⟩) hκ')) (fun i' => hst i' _ (hg' i')) (fun i' => by
        by_cases hi : i' = i
        · subst hi
          rw [← map_inv, ← map_mul, ← map_mul]
          refine hst i' _ ?_
          rw [mul_smul, mul_smul, hg, smul_comm (g' i') s, hg', ← hg, inv_smul_smul]
        · have hc := hcomm _ (hAt i (g s)) _ (GlobalTheory.FinPl.LocProd.grpAt_le_grpOff' _ _ _
            (fun w hw hw' => hi (hinj (hw.symm.trans hw'))) (hAt i' (g' i')))
          rw [mul_assoc, ← hc, inv_mul_cancel_left]
          exact hst i' _ (hg' i'))
    have hc := hcomm _ (hAt i (g s)) r (real_le_off _ _ hr)
    have h1' : κ * (β j i).gl (g s) = (β j i).gl (g s) * κ''.1 := h1
    have e1 : γ * (A.h j b c * r) * κ * (β j i).gl (g s) = γ * (A.h j b c * (β j i).gl (g s) * r * κ''.1) := by
      rw [mul_assoc, h1', mul_assoc (A.h j b c), hc]
      simp only [mul_assoc]
    rw [e1, hy' γ hγ, h2]
  simp only [key]
  rw [← mul_finsum' _ _ (Set.toFinite _), h0, mul_zero]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslateSumEqZeroOfChartRepresentativesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondTranslateSum_eq_zero_of_chartRepresentatives : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y, (∀ (c : {c // A.chOf j c = b}) y', ∑ᶠ s, A.rd θ j hj b φ y' (A.h j b c * (β j i).gl (g s)) = 0) → ∀ x, ∑ᶠ s, A.rd θ j hj b φ y (x * (β j i).gl (g s)) = 0 := by
  first | exact @GlobalTheory.AdForm.diaSum_eq_zero_of_reps | exact GlobalTheory.AdForm.diaSum_eq_zero_of_reps | (intros; apply GlobalTheory.AdForm.diaSum_eq_zero_of_reps <;> assumption)
end
end
