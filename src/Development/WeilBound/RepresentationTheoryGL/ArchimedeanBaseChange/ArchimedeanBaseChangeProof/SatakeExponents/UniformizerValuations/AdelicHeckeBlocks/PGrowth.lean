module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelRep
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.WdValAppend
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfTwist
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PTestJ

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Growth

theorem pow_words {A Γ J : Type} [Ring A] [Algebra ℂ A] [Fintype J] (g : Γ → A) (c : J → ℂ)
    (w : J → List Γ) (k : ℕ) :
    (∑ j, c j • ((w j).map g).prod) ^ k =
      ∑ f : Fin k → J, (∏ i, c (f i)) • (((List.ofFn fun i => w (f i)).flatten).map g).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ih, Finset.sum_mul_sum, ← (Fin.consEquiv fun _ => J).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun f _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      List.ofFn_succ, List.flatten_cons, List.map_append, List.prod_append, smul_mul_smul_comm]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]

theorem trM_add (Φ Ψ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (Φ + Ψ) M = trM Φ M + trM Ψ M := by
  funext y
  simp only [trM, Pi.add_apply, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem trM_smul (c : ℂ) (Φ : Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (c • Φ) M = c • trM Φ M := by
  funext y
  simp only [trM, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem trM_zero (M : Matrix ι ι ℂ) : trM (0 : Matrix ι ι (H E a b → ℂ)) M = 0 := by
  funext y
  simp [trM]

theorem trM_sum {J : Type} (s : Finset J) (c : J → ℂ) (Φ : J → Matrix ι ι (H E a b → ℂ)) (M : Matrix ι ι ℂ) :
    trM (∑ j ∈ s, c j • Φ j) M = ∑ j ∈ s, c j • trM (Φ j) M := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact trM_zero M
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, trM_add, trM_smul, ih]

end Growth

theorem blkGrowth (h1 : BlockOperatorsProductAdjoint) (h2 : BlockWordOperators) (h3 : BlockLinearCombinations) (h4 : EllLin) : BlockEllipticGrowth := by
  intro E _ _ _ _ B _ _ _ _ μ₁ _ μ₂ _ hG M t₁ t₂ J _ c w c₀ hc₀ ht₁ ht₂ hw
  obtain ⟨R, hR0, hRs⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ s : PT B, (s = t₁ ∨ ∃ j, Sum.inr s ∈ w j) → s.T ≤ R ∧ s.r + B.c ≤ R := by
    let gB : BGen B → ℝ := Sum.elim (fun _ => 0) fun s => |s.T| + |s.r + B.c|
    have gB0 : ∀ g, 0 ≤ gB g := by
      rintro (x | s)
      · exact le_refl 0
      · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hl0 : ∀ j, ∀ x ∈ (w j).map gB, 0 ≤ x := fun j x hx => by
      obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
      exact gB0 g
    have hs0 : 0 ≤ ∑ j, ((w j).map gB).sum := Finset.sum_nonneg fun j _ => List.sum_nonneg (hl0 j)
    refine ⟨gB (Sum.inr t₁) + ∑ j, ((w j).map gB).sum, add_nonneg (gB0 _) hs0, fun s hs => ?_⟩
    have key : gB (Sum.inr s) ≤ gB (Sum.inr t₁) + ∑ j, ((w j).map gB).sum := by
      rcases hs with rfl | ⟨j, hj⟩
      · linarith
      · have e1 : gB (Sum.inr s) ≤ ((w j).map gB).sum := List.single_le_sum (hl0 j) _ (List.mem_map.2 ⟨_, hj, rfl⟩)
        have e2 : ((w j).map gB).sum ≤ ∑ j, ((w j).map gB).sum :=
          Finset.single_le_sum (f := fun j => ((w j).map gB).sum) (fun j _ => List.sum_nonneg (hl0 j)) (Finset.mem_univ j)
        linarith [gB0 (Sum.inr t₁)]
    have e : gB (Sum.inr s) = |s.T| + |s.r + B.c| := rfl
    constructor <;> linarith [le_abs_self s.T, le_abs_self (s.r + B.c), abs_nonneg s.T, abs_nonneg (s.r + B.c)]
  obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ j, (w j).length ≤ L :=
    ⟨Finset.univ.sup fun j => (w j).length, fun j => Finset.le_sup (f := fun j => (w j).length) (Finset.mem_univ j)⟩
  have hr₀ : 0 ≤ c₀ * (1 + t₂.T + R) + t₂.r + R := by
    have := mul_nonneg hc₀ (by linarith [ht₂.T] : 0 ≤ 1 + t₂.T + R)
    linarith [ht₂.r]
  have hr₁ : 0 ≤ (c₀ + 1) * L * R := mul_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hR0
  obtain ⟨C, N, hCN⟩ := hG t₁.Φ t₂.Φ t₁.op t₂.op M _ _ (h1 E B t₁ t₁ ht₁ ht₁).1 (h1 E B t₂ t₂ ht₂ ht₂).1
    (h1 E B t₁ t₁ ht₁ ht₁).2.1 (h1 E B t₂ t₂ ht₂ ht₂).2.1 hr₀ hr₁
  refine ⟨C, N, fun k hk => ?_⟩
  have hf : ∀ f : Fin k → J,
      IsTestM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ ∧
      IsROp B.D (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ
        (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op ∧
      BGen.sc (List.ofFn fun i => w (f i)).flatten • (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op =
        t₁.op * (((List.ofFn fun i => w (f i)).flatten).map BGen.op).prod * t₂.op ∧
      D4.IsTest2J (trM (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ M)
        (c₀ * (1 + t₂.T + R) + t₂.r + R + k * ((c₀ + 1) * L * R)) := by
    intro f
    have hmem : ∀ g ∈ (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten), BGen.Ok g := by
      intro g hg
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ht₁
      · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.1 hg
        rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl
        exact hw (f i) g hgl
    have hRw : ∀ s, Sum.inr s ∈ (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) → s.T ≤ R ∧ s.r + B.c ≤ R := by
      intro s hs
      apply hRs s
      rcases List.mem_cons.1 hs with h | h
      · exact Or.inl (Sum.inr_injective h)
      · obtain ⟨l, hl, hgl⟩ := List.mem_flatten.1 h
        rw [List.mem_ofFn] at hl
        obtain ⟨i, rfl⟩ := hl
        exact Or.inr ⟨f i, hgl⟩
    obtain ⟨ok, hop, hT, hr, -, -⟩ := h2 E B _ t₂ R hmem ht₂ hR0 hRw
    have hlenN : ((List.ofFn fun i => w (f i)).flatten).length ≤ k * L := by
      rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
      refine (Finset.sum_le_sum fun i _ => ?_).trans (le_of_eq (by simp : ∑ _i : Fin k, L = k * L))
      exact hL (f i)
    have hlen : ((Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten).length : ℝ) ≤ 1 + k * L := by
      have := (Nat.cast_le (α := ℝ)).2 hlenN
      push_cast at this
      simp only [List.length_cons]
      push_cast
      linarith
    refine ⟨(h1 E B _ _ ok ok).1, (h1 E B _ _ ok ok).2.1, ?_, ?_⟩
    · have e := Word.sc_inr t₁ (List.ofFn fun i => w (f i)).flatten
      rw [← e, ← hop, List.map_cons, List.prod_cons]
      rfl
    · apply CG.isTest2J_mono (hk f _ rfl)
      have a1 := mul_le_mul_of_nonneg_right hlen hR0
      have a2 := mul_le_mul_of_nonneg_left
        (hT.trans (by linarith : t₂.T + _ * R ≤ t₂.T + (1 + k * L) * R)) hc₀
      linarith
  have hsum := h3 E B.a B.b B.D B.I (Fin k → J) Finset.univ
    (fun f => (∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten)
    (fun f => (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ)
    (fun f => (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op) (fun f _ => ⟨(hf f).1, (hf f).2.1⟩)
  have hopEq : ∑ f : Fin k → J, ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) •
      (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).op =
      t₁.op * (∑ j, c j • ((w j).map BGen.op).prod) ^ k * t₂.op := by
    rw [Growth.pow_words, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [mul_smul, (hf f).2.2.1, mul_smul_comm, smul_mul_assoc]
  have hrop : IsROp B.D (∑ f : Fin k → J, ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) •
      (BGen.wd (Sum.inr t₁ :: (List.ofFn fun i => w (f i)).flatten) t₂).Φ) (t₁.op * (∑ j, c j • ((w j).map BGen.op).prod) ^ k * t₂.op) := by
    rw [← hopEq]
    exact hsum.2
  have htest := CG.isTest2J_sum (Finset.univ : Finset (Fin k → J)) fun f _ =>
    CG.isTest2J_smul ((∏ i, c (f i)) * BGen.sc (List.ofFn fun i => w (f i)).flatten) (hf f).2.2.2
  rw [← Growth.trM_sum] at htest
  have hb := hCN k _ _ hsum.1 hrop htest
  have hnn : 0 ≤ c₀ * (1 + t₂.T + R) + t₂.r + R + k * ((c₀ + 1) * L * R) :=
    add_nonneg hr₀ (mul_nonneg (Nat.cast_nonneg _) hr₁)
  rw [Growth.trM_sum, h4 E B.a B.b μ₁ μ₂ (Fin k → J) Finset.univ _ _ _ hnn fun f _ => (hf f).2.2.2] at hb
  exact hb

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.AdelRep
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Adel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

omit [IsCMField E] in
theorem cpt_eq (w : Pl E) (u : GL (Fin n) E) (x : GA E n) :
    cpt w u x = GeneralLinearGroup.map (pLoc E w) (gFin x * (ratF E n u)⁻¹) := by
  rw [cpt, adeleqof_map_cW, map_mul, map_inv, adeleqof_pFin_ratGL]; rfl

theorem cpt'_eq (w : Pl E) (u : GL (Fin n) E) (x : GA E n) :
    cpt' w u x = GeneralLinearGroup.map (pLoc E w) (thF E n (gFin x * (ratF E n u)⁻¹)) := by
  rw [cpt', adeleqof_map_cW, adeleqof_pFin_thetaGL, map_mul, map_inv, adeleqof_pFin_ratGL]; rfl

end Adel

theorem rtAlg (hS : SizeBasic) : RtAlg := by
  intro E _ _ _ B u₁ u₂
  refine ⟨?_, ?_, ?_⟩
  · intro ψ ψ'
    funext x y g
    simp only [mulF, rt, mul_assoc]
  · intro t ht
    refine ⟨t.r + B.c + |logSize (finGL E B.a (ratF E B.a u₁))| + |logSize (finGL E B.b (ratF E B.b u₂))|, ?_⟩
    refine ⟨ht.T, add_nonneg (add_nonneg (add_nonneg ht.r B.c_nonneg) (abs_nonneg _)) (abs_nonneg _), ht.ka, ht.kb,
      fun x y => ⟨(ht.ψ x y).1.comp (continuous_mul_const _),
        (ht.ψ x y).2.comp_homeomorph (Homeomorph.mulRight (ratF E B.a u₁, ratF E B.b u₂)⁻¹)⟩, ?_⟩
    intro x y h hne
    have hh := ht.size x y _ hne
    simp only [Prod.fst_mul, Prod.fst_inv, Prod.snd_mul, Prod.snd_inv] at hh
    obtain ⟨h1, h2⟩ := hh
    have e1 : finGL E B.a h.1 = finGL E B.a (h.1 * (ratF E B.a u₁)⁻¹) * finGL E B.a (ratF E B.a u₁) := by
      rw [← map_mul, inv_mul_cancel_right]
    have e2 : finGL E B.b h.2 = finGL E B.b (h.2 * (ratF E B.b u₂)⁻¹) * finGL E B.b (ratF E B.b u₂) := by
      rw [← map_mul, inv_mul_cancel_right]
    have c1 := B.ca (finGL E B.a (h.1 * (ratF E B.a u₁)⁻¹)) (finGL E B.a (ratF E B.a u₁))
    have c2 := B.cb (finGL E B.b (h.2 * (ratF E B.b u₂)⁻¹)) (finGL E B.b (ratF E B.b u₂))
    have a1 := le_abs_self (logSize (finGL E B.a (ratF E B.a u₁)))
    have a2 := le_abs_self (logSize (finGL E B.b (ratF E B.b u₂)))
    have p1 := abs_nonneg (logSize (finGL E B.a (ratF E B.a u₁)))
    have p2 := abs_nonneg (logSize (finGL E B.b (ratF E B.b u₂)))
    rw [e1, e2]
    constructor <;> · dsimp only; linarith
  · intro ψ hψ
    choose ra hra using fun x y => (hS E B.a).1 _
      ((hψ x y).2.image ((continuous_finGL' (E := E) B.a).comp continuous_fst))
    choose rb hrb using fun x y => (hS E B.b).1 _
      ((hψ x y).2.image ((continuous_finGL' (E := E) B.b).comp continuous_snd))
    refine ⟨∑ x, ∑ y, (|ra x y| + |rb x y|), Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity, ?_⟩
    intro x y h hne
    have key : |ra x y| + |rb x y| ≤ ∑ x, ∑ y, (|ra x y| + |rb x y|) :=
      (Finset.single_le_sum (f := fun y' => |ra x y'| + |rb x y'|) (fun _ _ => by positivity) (Finset.mem_univ y)).trans
        (Finset.single_le_sum (f := fun x' => ∑ y', (|ra x' y'| + |rb x' y'|))
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ x))
    have hm : h ∈ tsupport (ψ x y) := subset_tsupport _ hne
    have b1 : logSize (finGL E B.a h.1) ≤ ra x y := hra x y _ ⟨h, hm, rfl⟩
    have b2 : logSize (finGL E B.b h.2) ≤ rb x y := hrb x y _ ⟨h, hm, rfl⟩
    have := le_abs_self (ra x y)
    have := le_abs_self (rb x y)
    have := abs_nonneg (ra x y)
    have := abs_nonneg (rb x y)
    exact ⟨by linarith, by linarith⟩

theorem adelRep (h1 : FmAlg) (h2 : FmTr) (h3 : RtAlg) : AdelRep := by
  intro E _ _ _ κ _ S P B e hS hP hne u₁ u₂ Ta Tb N Lo w t₀ L₀ hLo hL₀ ht₀
  have key : (lmWd Lo w L₀).Ok P ∧ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e (lmWd Lo w L₀)) := by
    induction w with
    | nil => exact ⟨hL₀, ht₀⟩
    | cons g w ih =>
      have ih' := ih (fun s hs => hLo s (List.mem_cons_of_mem _ hs))
      rcases g with c | s
      · exact ih'
      · obtain ⟨hs1, hs2⟩ := hLo s (by simp)
        obtain ⟨-, hB, hC, -, -⟩ := h1 E κ S P B e hS hP (Lo s) (lmWd Lo w L₀) hs1 ih'.1
        refine ⟨hB, ?_⟩
        show mulF B.ν s.ψ (BGen.wd w t₀).ψ = rt u₁ u₂ (fm S P B e ((Lo s).mul (lmWd Lo w L₀)))
        rw [ih'.2, hs2, (h3 E B u₁ u₂).1, hC]
  refine ⟨key.1, key.2, ?_⟩
  funext g
  obtain ⟨-, hT⟩ := h2 E κ S P B e hP hne (lmWd Lo w L₀) N key.1
  have hT3 : F.trM (BGen.wd w t₀).Φ (opM Ta Tb (tenN P B e N)) g = _ :=
    tensTr E B.a B.b B.Ma B.Mb B.κ (BGen.wd w t₀).ka (BGen.wd w t₀).kb Ta Tb (BGen.wd w t₀).ψ (tenN P B e N) g
  have hA : ∏ v, (BGen.wd w t₀).arch Ta Tb v (GeneralLinearGroup.map (cV v) g.1, GeneralLinearGroup.map (cV v) g.2) =
      (∏ v, phiOf (B.Ma v) (Ta v) ((BGen.wd w t₀).ka v) (gInf v g.1)) *
        ∏ v, phiOf (B.Mb v) (Tb v) ((BGen.wd w t₀).kb v) (gInf v g.2) := by
    simp only [PT.arch]
    exact Finset.prod_mul_distrib
  have hF : finFn S ((lmWd Lo w L₀).tr P N) (lmWd Lo w L₀).t (hFin g * (ratF E B.a u₁, ratF E B.b u₂)⁻¹) =
      ∏ᶠ v ∈ S, (lmWd Lo w L₀).tr P N v (cpt v u₁ g.1, cpt v u₂ g.2) *
        if IsSplitAt v then (lmWd Lo w L₀).t v (cpt' v u₁ g.1, cpt' v u₂ g.2) else 1 := by
    simp only [finFn, Adel.cpt_eq, Adel.cpt'_eq]
    rfl
  rw [hT3, key.2]
  simp only [rt]
  rw [hT, Pi.smul_apply, smul_eq_mul, adel, hA, hF]
  ring

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.NrmLCharpoly
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.PPolEq
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host
open GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.G8

theorem poleq_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : GL (Fin n) E)
    (hu : IsTransl u) (d : GL (Fin n) E) : d * u⁻¹ * thE E n (d * u⁻¹) = nrm d := by
  have h2 : thetaE E n u = u⁻¹ := eq_inv_of_mul_eq_one_right hu.2
  rw [hu.1, map_mul, map_inv, h2, nrm]
  group

end PositivityTheory.Rg.BcB.G8

end
end

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.BCT PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH

namespace Reg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

open PositivityTheory.Rg.Tf.Loc (twConj)

theorem nrmL_charpoly {w : Pl E} (hw : ¬ IsSplitAt w) {u : GL (Fin n) E} (hu : IsTransl u) (d : GL (Fin n) E)
    (x : GA E n) :
    (nrmL n w (GeneralLinearGroup.map (pLoc E w) (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹))).val.charpoly
      = (nrm d).val.charpoly.map (algebraMap E (w.adicCompletion E)) := by
  set c := GeneralLinearGroup.map (pFin E) x
  have h1 : GeneralLinearGroup.map (pLoc E w) (gFin (twConj (thetaA E n) x (ratGL E n d)) * (ratF E n u)⁻¹) =
      GeneralLinearGroup.map (pLoc E w) (c⁻¹ * ratF E n (d * u⁻¹) * thF E n c) := by
    rw [← adeleqof_cpt translAd_holds hu d x w, cpt, adeleqof_map_cW]
    congr 1
    rw [map_mul, map_inv, adeleqof_pFin_ratGL]
    rfl
  set r := ratF E n (d * u⁻¹) with hr0
  set s := ratF E n (thE E n (d * u⁻¹)) with hs0
  have hr : thF E n r = s := by
    rw [hr0, hs0]
    rw [GlobalTheory.EulerTw.Comm.thF_ratF]
  have h2 : (c⁻¹ * r * thF E n c) * thF E n (c⁻¹ * r * thF E n c) = c⁻¹ * ratF E n (nrm d) * c := by
    rw [← poleq_norm E n u hu d, map_mul (ratF E n), ← hr0, ← hs0, map_mul, map_mul, map_inv,
      GlobalTheory.EulerTw.Comm.thF_thF, hr]
    group
  have h3 : nrmL n w (GeneralLinearGroup.map (pLoc E w) (c⁻¹ * r * thF E n c)) =
      GeneralLinearGroup.map (pLoc E w) (c⁻¹ * ratF E n (nrm d) * c) := by
    have hz : ∀ g, thetaGL n (cj w) (GeneralLinearGroup.map (pLoc E w) g) = GeneralLinearGroup.map (pLoc E w) (thF E n g) := by
      intro g; rw [GlobalTheory.CompanionTheory.SuppFinTw.map_thF_of_not_split hw, thL, if_neg hw]
    rw [nrmL, if_neg hw, hz, ← map_mul, h2]
  rw [h1, h3, map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']
  rw [← Matrix.charpoly_map]
  rfl

theorem val_mem {m : ℕ} (y : GL (Fin m) ℂ) : y.val ∈ GLs m := by
  show y.val.det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp y.isUnit).ne_zero

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem phiOf_cont {m : ℕ} [MeasurableSpace (G m)] {μ : Measure (G m)} {M : KMod m} (Tθ : M.V →L[ℂ] M.V)
    {k : Mat m → (M.V →L[ℂ] M.V)} {val} {T : ℝ} (hM : IsMult μ M k val T) : Continuous (phiOf M Tθ k) := by
  obtain ⟨l, c, w, g, ks, hks, hk, -⟩ := hM
  set F : GL (Fin m) ℂ → (M.V →L[ℂ] M.V) := fun y => ∑ i, c i • ks i y.val with hFdef
  have hkF : ∀ y : GL (Fin m) ℂ, k y.val = F y := fun y => hk _ (val_mem y)
  have hF : Continuous F := continuous_finsetSum _ fun i _ =>
    (((hks i).2.1.continuousOn).comp_continuous Units.continuous_val fun y => val_mem y).const_smul (c i)
  let L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ := (LinearMap.trace ℂ M.V).comp (ContinuousLinearMap.coeLM ℂ)
  have hphi : phiOf M Tθ k = fun y => L (F y * Tθ) := by
    funext y
    rw [← hkF]
    rfl
  rw [hphi]
  exact L.continuous_of_finiteDimensional.comp (hF.mul continuous_const)

theorem phiOf_lg {m : ℕ} {M : KMod m} (Tθ : M.V →L[ℂ] M.V) {k : Mat m → (M.V →L[ℂ] M.V)} (c T : ℝ)
    (hk : ∀ y ∈ GLs m, c * (1 + T) < lg y → k y = 0) (y : G m) (hy : phiOf M Tθ k y ≠ 0) : lg y.val ≤ c * (1 + T) := by
  by_contra h
  push Not at h
  apply hy
  rw [phiOf, hk _ (val_mem y) h, zero_mul]
  simp

end Reg

open PositivityTheory.Rg.Tf.Loc (twConj) in
theorem regOf : RegOf := by
  intro E _ _ _ a b S u₁ u₂ hu₁ hu₂ φ₁ φ₂ h₁ h₂ hw
  obtain ⟨w, hwS, hns, hreg⟩ := hw
  refine ⟨fun d x h₂' hne => ?_, fun d x h₁' hne => ?_⟩
  · have hf := (GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ _ hne w hwS).1
    have hs1 := Polynomial.Separable.of_mul_left (hreg _ hf)
    change (nrmL a w (GeneralLinearGroup.map (pLoc E w)
      (gFin (twConj (thetaA E a) x (ratGL E a d)) * (ratF E a u₁)⁻¹))).val.charpoly.Separable at hs1
    rw [Reg.nrmL_charpoly hns hu₁] at hs1
    exact (Polynomial.separable_map _).1 hs1
  · have hf := (GlobalTheory.CompanionTheory.SuppFinTw.factors_ne h₁ h₂ _ hne w hwS).1
    have hs1 := Polynomial.Separable.of_mul_right (hreg _ hf)
    change (nrmL b w (GeneralLinearGroup.map (pLoc E w)
      (gFin (twConj (thetaA E b) x (ratGL E b d)) * (ratF E b u₂)⁻¹))).val.charpoly.Separable at hs1
    rw [Reg.nrmL_charpoly hns hu₂] at hs1
    exact (Polynomial.separable_map _).1 hs1

theorem pTTest (h0 : RegOf) (h1 : FinConv) (h2 : FmTr) (hk : KerEx) : PTTest := by
  intro E _ _ _ B
  have := B.ha
  have := B.hb
  have : BorelSpace (G B.a) := ⟨rfl⟩
  have : BorelSpace (G B.b) := ⟨rfl⟩
  obtain ⟨ca, hca⟩ := hk B.a
  obtain ⟨cb, hcb⟩ := hk B.b
  set c₀ : ℝ := max 0 (max ca cb) with hc₀
  have hc₀0 : 0 ≤ c₀ := le_max_left _ _
  refine ⟨2 * Fintype.card (InfinitePlace E) * c₀, by positivity, ?_⟩
  intro κ _ S P e hS hPS hne u₁ u₂ hu₁ hu₂ Ta Tb N t L hVC ht hL hψ hreg
  set γ : Hf E B.a B.b := (ratF E B.a u₁, ratF E B.b u₂) with hγ
  obtain ⟨hTr, hFm⟩ := h2 E κ S P B e hPS hne L N hL
  obtain ⟨-, hFC⟩ := h1 E B S hS
  obtain ⟨hcs, ⟨U, hUo, hU⟩, -⟩ := hFC (L.tr P N) L.t hTr hL.2
  set Ψ : Hf E B.a B.b → ℂ := fun h => B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹) with hΨ
  have hΨeq : ∀ h, ∑ x, ∑ y, t.ψ x y h * tenN P B e N y x = Ψ h := by
    intro h
    rw [hψ]
    exact hFm (h * γ⁻¹)
  have hT1 : 0 ≤ 1 + t.T := by linarith [ht.T]
  have hR0 : 0 ≤ c₀ * (1 + t.T) := mul_nonneg hc₀0 hT1
  have hfa : ∀ v, Continuous (phiOf (B.Ma v) (Ta v) (t.ka v)) ∧ VeryCusp (phiOf (B.Ma v) (Ta v) (t.ka v)) ∧
      ∀ y, phiOf (B.Ma v) (Ta v) (t.ka v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
    ⟨Reg.phiOf_cont _ (ht.ka v), hVC.1 v _ _ _ (ht.ka v), fun y hy =>
      (Reg.phiOf_lg _ ca t.T ((hca B.μa (B.Ma v)).2 _ _ t.T ht.T (ht.ka v)) y hy).trans
        (mul_le_mul_of_nonneg_right ((le_max_left ca cb).trans (le_max_right _ _)) hT1)⟩
  have hfb : ∀ v, Continuous (phiOf (B.Mb v) (Tb v) (t.kb v)) ∧ VeryCusp (phiOf (B.Mb v) (Tb v) (t.kb v)) ∧
      ∀ y, phiOf (B.Mb v) (Tb v) (t.kb v) y ≠ 0 → lg y.val ≤ c₀ * (1 + t.T) := fun v =>
    ⟨Reg.phiOf_cont _ (ht.kb v), hVC.2 v _ _ _ (ht.kb v), fun y hy =>
      (Reg.phiOf_lg _ cb t.T ((hcb B.μb (B.Mb v)).2 _ _ t.T ht.T (ht.kb v)) y hy).trans
        (mul_le_mul_of_nonneg_right ((le_max_right ca cb).trans (le_max_right _ _)) hT1)⟩
  have hsz : ∀ h, Ψ h ≠ 0 → logSize (finGL E B.a h.1) ≤ t.r ∧ logSize (finGL E B.b h.2) ≤ t.r := by
    intro h hh
    rw [← hΨeq] at hh
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hh
    obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact ht.size x y h (left_ne_zero_of_mul hy)
  have hfin : ∀ g, Ψ g ≠ 0 → finFn S (L.tr P N) L.t (g * γ⁻¹) ≠ 0 := fun g hg => right_ne_zero_of_mul hg
  obtain ⟨hr₁, hr₂⟩ := h0 E B.a B.b S u₁ u₂ hu₁ hu₂ (L.tr P N) L.t hTr hL.2 hreg
  set U' : Subgroup (Hf E B.a B.b) := U ⊓ U.comap (MulAut.conj γ).toMonoidHom with hU'
  have hU'o : IsOpen (U' : Set (Hf E B.a B.b)) := by
    rw [hU', Subgroup.coe_inf, Subgroup.coe_comap]
    exact hUo.inter (hUo.preimage (by
      show Continuous fun x : Hf E B.a B.b => γ * x * γ⁻¹
      fun_prop))
  have hΨU : ∀ u ∈ U', ∀ h, Ψ (u * h) = Ψ h ∧ Ψ (h * u) = Ψ h := by
    intro u hu h
    have hc : γ * u * γ⁻¹ ∈ U := hu.2
    have e : h * u * γ⁻¹ = h * γ⁻¹ * (γ * u * γ⁻¹) := by group
    refine ⟨?_, ?_⟩
    · show B.vol⁻¹ * finFn S (L.tr P N) L.t (u * h * γ⁻¹) = B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹)
      rw [mul_assoc u h, (hU u hu.1 _).1]
    · show B.vol⁻¹ * finFn S (L.tr P N) L.t (h * u * γ⁻¹) = B.vol⁻¹ * finFn S (L.tr P N) L.t (h * γ⁻¹)
      rw [e, (hU _ hc _).2]
  have hcsΨ : HasCompactSupport Ψ :=
    (hcs.comp_homeomorph (Homeomorph.mulRight γ⁻¹)).mul_left (f := fun _ => B.vol⁻¹)
  have key := PositivityTheory.Rg.BcB.CG.test2J E B.a B.b (fun v => phiOf (B.Ma v) (Ta v) (t.ka v))
    (fun v => phiOf (B.Mb v) (Tb v) (t.kb v)) Ψ (c₀ * (1 + t.T)) t.r U' hR0 hfa hfb hcsΨ hU'o hΨU hsz
    (fun d x h₂ hne => hr₁ d x h₂ (hfin _ hne)) (fun d x h₁ hne => hr₂ d x h₁ (hfin _ hne))
  have hfun : trM t.Φ (opM Ta Tb (tenN P B e N)) = fun g =>
      (∏ v, phiOf (B.Ma v) (Ta v) (t.ka v) (gInf v g.1)) * (∏ v, phiOf (B.Mb v) (Tb v) (t.kb v) (gInf v g.2)) *
        Ψ (hFin g) := by
    funext g
    rw [PT.Φ, PositivityTheory.Rg.BcB.CG.tensTr, hΨeq]
  rw [hfun]
  exact PositivityTheory.Rg.BcB.CG.isTest2J_mono key (le_of_eq (by ring))

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.AdjKer0
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG borelF borelH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Sq

end Sq

theorem sqOk (h0 : AdjKer0) (h1 : BlockOperatorsProductAdjoint) (h2 : BlockWordOperators) : SqOk := by
  intro E _ _ _ B t g m ht hg hka hkb
  obtain ⟨-, -, -, -, hadjOk, hadjOp, -, -⟩ := h1 E B t t ht ht
  have hmult : ∀ {n : ℕ} (μ : Measure (G n)), μ.IsHaarMeasure → ∀ (M : Mods E n) (k : Kers M)
      (va : InfinitePlace E → Inf n → ℂ), (∀ v, IsKer μ (M v) [] g (k v) ∧ ∀ χ, va v χ = coshT g (cas χ)) →
      IsMults μ (adjK k) va t.T := by
    intro n μ hμ M k va h v
    refine ⟨1, fun _ => 1, fun _ => [], fun _ => g, fun _ => adjK k v,
      fun _ => ⟨hg, h0 n μ hμ (M v) g t.T (k v) hg (h v).1⟩, ?_, ?_⟩
    · intro y _
      simp
    · intro χ
      simp [zVal, (h v).2 χ]
  have hadj' : t.adj'.Ok :=
    ⟨ht.T, ht.r, hmult B.μa B.ha B.Ma t.ka t.va hka, hmult B.μb B.hb B.Mb t.kb t.vb hkb, hadjOk.ψ, hadjOk.size⟩
  have hw : ∀ s : PT B, s.Ok → (s.pw m).Ok ∧ (s.pw m).op = s.op ^ (m + 1) ∧
      ∀ χa χb, (s.pw m).val χa χb = s.val χa χb ^ (m + 1) := by
    intro s hs
    obtain ⟨hO, hop, -, -, -, hval⟩ := h2 E B (List.replicate m (Sum.inr s)) s (max s.T (s.r + B.c))
      (fun x hx => by rw [List.eq_of_mem_replicate hx]; exact hs) hs (le_max_of_le_left hs.T)
      (fun s' hs' => by
        cases Sum.inr.inj (List.eq_of_mem_replicate hs')
        exact ⟨le_max_left _ _, le_max_right _ _⟩)
    refine ⟨hO, ?_, ?_⟩
    · simp [BGen.sc, BGen.op, List.map_replicate, List.prod_replicate] at hop
      rw [pow_succ]
      exact hop.symm
    · intro χa χb
      have e := hval χa χb
      simp [List.map_replicate, List.prod_replicate] at e
      rw [pow_succ]
      exact e
  obtain ⟨hpO, hpop, hpval⟩ := hw t ht
  obtain ⟨haO, haop, haval⟩ := hw t.adj' hadj'
  obtain ⟨-, -, hmO, hmop, -, -, hmval, -⟩ := h1 E B (t.adj'.pw m) (t.pw m) haO hpO
  have eop : t.adj'.op = t.adj.op := rfl
  have evl : ∀ χa χb, t.adj'.val χa χb = t.val χa χb := fun _ _ => rfl
  refine ⟨hpO, hpop, hmO, ?_, ?_, rfl⟩
  · show ((t.adj'.pw m).mul (t.pw m)).op = _
    rw [hmop, haop, hpop, eop, hadjOp, star_pow, ContinuousLinearMap.star_eq_adjoint]
  · intro χa χb
    show ((t.adj'.pw m).mul (t.pw m)).val χa χb = _
    rw [hmval, haval, hpval, evl, ← pow_add, two_mul]

end PositivityTheory.Rg.BcB.F

end
end
