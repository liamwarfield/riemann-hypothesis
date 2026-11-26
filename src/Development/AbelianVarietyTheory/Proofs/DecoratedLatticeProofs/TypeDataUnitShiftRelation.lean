module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNorms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7}

section Lin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k}
  {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def sOpLin (β : Frame p S n) (P : Pair k n) (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) :
    (GA D S → ℂ) →ₗ[ℂ] (GA D S → ℂ) where
  toFun := sOp β P q χ ε
  map_add' a b := by
    have h : formAt β P (a + b) = formAt β P a + formAt β P b := by
      funext P₁; simp [formAt, map_add (f := _)]
    simp only [sOp, h, map_add (f := _), Pi.add_apply]
  map_smul' c a := by
    have h : formAt β P (c • a) = c • formAt β P a := by
      funext P₁; simp [formAt, map_smul]
    simp only [sOp, h, map_smul, Pi.smul_apply, RingHom.id_apply]

end Lin

variable {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem S_lin (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) :
    ∃ L : (GA D (c.X j) → ℂ) →ₗ[ℂ] (GA D (c.X j) → ℂ), ∀ f, o.S ε j f = L f := by
  refine ⟨o.I.foldr (fun i G => (sOpLin (o.β j i) (o.Q j i) o.q (resChar (o.χ i) (o.hχ i) o.q) (ε j i)).comp G)
    LinearMap.id, fun f => ?_⟩
  unfold TDat.S
  induction o.I with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih]; rfl

theorem S_smul (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) (a : ℂ) (f : GA D (c.X j) → ℂ) :
    o.S ε j (a • f) = a • o.S ε j f := by
  obtain ⟨L, hL⟩ := S_lin o ε j
  rw [hL, hL, map_smul]

theorem S_sum (o : TDat c k ι) (ε : ℕ → ι → 𝓀[k]ˣ) (j : ℕ) {α : Type} (s : Finset α) (f : α → GA D (c.X j) → ℂ) :
    o.S ε j (∑ a ∈ s, f a) = ∑ a ∈ s, o.S ε j (f a) := by
  obtain ⟨L, hL⟩ := S_lin o ε j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hL, map_sum]; simp only [hL]

theorem lift_smul {S T : HSp D} (kd : KerDat S T) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (x : DefSp S) (y : DefSp T)
    (P : PolF D T.rank S.rank) (a : ℂ) (φ : GA D S → ℂ) :
    kd.lift ψ θ x y P (a • φ) = a • kd.lift ψ θ x y P φ := by
  funext h
  simp only [KerDat.lift, liftT_apply, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext g; ring

end GlobalTheory.SeeSaw.MoveZero

noncomputable section

namespace GlobalTheory.SeeSaw.MoveZero

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem col_zero (t : Tup c) (ψ : t.Col 0) : t.col 0 ψ = ψ := rfl

theorem col_succ (t : Tup c) (j : ℕ) (ψ : t.Col 0) : t.col (j + 1) ψ = t.K j (t.col j ψ) := rfl

theorem col_mem (t : Tup c) (hI : t.Is) : ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.col j ψ ∈ t.Ram j := by
  intro j
  induction j with
  | zero => intro _ ψ hψ; exact hψ
  | succ j ih =>
    intro hj ψ hψ
    rw [col_succ]
    exact hI.stabK j (by omega) _ (ih (by omega) ψ hψ)

theorem iterS_mem (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hR : ReadS o t ε S₀) : ∀ i, ∀ ψ ∈ t.Ram 0, iterS S₀ ε i ψ ∈ t.Ram 0 := by
  intro i
  induction i with
  | zero => intro ψ hψ; exact hψ
  | succ i ih => intro ψ hψ; exact (hR.S₀ _ _ (ih ψ hψ)).1

theorem stepK (t : Tup c) (hK : t.KBack) {j : ℕ} (hj : j < D.R.m) {a b : t.Col j} (ha : a ∈ t.Ram j) (hb : b ∈ t.Ram j)
    (x : ℂ) (h : ∀ α y, t.rd j α a y = x • t.rd j α b y) :
    ∀ γ y', t.rd (j + 1) γ (t.K j a) y' = x • t.rd (j + 1) γ (t.K j b) y' := by
  intro γ y'
  obtain ⟨hc, hB⟩ := hK j hj
  obtain ⟨n, y, P, hP⟩ := hB y'
  have e1 := hP a ha γ
  simp_rw [h, lift_smul, ← Finset.smul_sum, ← hP b hb γ] at e1
  rw [smul_comm] at e1
  exact smul_right_injective _ hc e1

theorem stepB (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) (η : ι → 𝓀[k]ˣ) :
    ∀ j, j ≤ D.R.m → ∀ ψ ∈ t.Ram 0, ∀ α y, o.S (fun _ => η) j (t.rd j α (t.col j ψ) y) =
      (∏ l ∈ Finset.range j, o.cL l) • t.rd j α (t.col j (S₀ η ψ)) y := by
  intro j
  induction j with
  | zero =>
    intro _ ψ hψ α y
    rw [Finset.range_zero, Finset.prod_empty, one_smul, col_zero, col_zero]
    exact ((hR.S₀ η ψ hψ).2 α y).symm
  | succ j ih =>
    intro hj ψ hψ γ y'
    have hj' : j < D.R.m := by omega
    obtain ⟨hc, hB⟩ := hK j hj'
    obtain ⟨n, y, P, hP⟩ := hB y'
    have m1 := col_mem t hI j hj'.le ψ hψ
    have m2 := col_mem t hI j hj'.le _ (hR.S₀ η ψ hψ).1
    have e1 := hP _ m1 γ
    have e2 := hP _ m2 γ
    apply smul_right_injective _ hc
    show t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y') =
      t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y')
    calc t.cK j • o.S (fun _ => η) (j + 1) (t.rd (j + 1) γ (t.K j (t.col j ψ)) y')
        = o.S (fun _ => η) (j + 1) (t.cK j • t.rd (j + 1) γ (t.K j (t.col j ψ)) y') := by rw [S_smul]
      _ = ∑ a, ∑ α, o.S (fun _ => η) (j + 1) ((t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j ψ) (y a))) := by
          rw [e1, S_sum]; simp only [S_sum]
      _ = ∑ a, ∑ α, (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.ker j α γ).lift c.ψ c.θ (c.x j) (c.x (j + 1)) (P a)
            (t.rd j α (t.col j (S₀ η ψ)) (y a)) := by
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun α _ => ?_
          rw [(hL j hj' α γ (P a) _ (hR.ram j hj'.le _ m1 α (y a))).2 η, ih hj'.le ψ hψ α (y a), lift_smul, smul_smul]
      _ = (o.cL j * ∏ l ∈ Finset.range j, o.cL l) • (t.cK j • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [e2]; simp only [Finset.smul_sum]
      _ = t.cK j • ((∏ l ∈ Finset.range (j + 1), o.cL l) • t.rd (j + 1) γ (t.K j (t.col j (S₀ η ψ))) y') := by
          rw [Finset.prod_range_succ, smul_comm, mul_comm]

theorem stepC (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0)
    (hI : t.Is) (hK : t.KBack) (hL : LiftS o t) (hR : ReadS o t ε S₀) :
    ∀ i, 2 * i ≤ D.R.m → ∀ ψ ∈ t.Ram 0, t.up i ψ ∈ t.Ram (2 * i) ∧
      ∀ α y, t.rd (2 * i) α (t.up i ψ) y = o.cS i • t.rd (2 * i) α (t.col (2 * i) (iterS S₀ ε i ψ)) y := by
  intro i
  induction i with
  | zero =>
    intro _ ψ hψ
    refine ⟨hψ, fun α y => ?_⟩
    simp only [TDat.cS, Finset.range_zero, Finset.prod_empty, one_smul]
    rfl
  | succ i ih =>
    intro hi ψ hψ
    obtain ⟨hu, hr⟩ := ih (by omega) ψ hψ
    have hφ := iterS_mem o t ε S₀ hR i ψ hψ
    have hS := hI.stabS (2 * i) (by omega) _ hu
    have hw := col_mem t hI (2 * i) (by omega) _ (hR.S₀ (ε (2 * i)) _ hφ).1
    have hv := col_mem t hI (2 * i) (by omega) _ hφ
    have h0 : ∀ α y, t.rd (2 * i) α (t.S (2 * i) (t.up i ψ)) y =
        (o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l) •
          t.rd (2 * i) α (t.col (2 * i) (S₀ (ε (2 * i)) (iterS S₀ ε i ψ))) y := by
      intro α y
      rw [hR.S (2 * i) (by omega) _ hu α y, hr α y, S_smul, mul_smul]
      congr 1
      exact stepB o t ε S₀ hI hK hL hR (ε (2 * i)) (2 * i) (by omega) _ hφ α y
    have h1 := stepK t hK (j := 2 * i) (by omega) hS hw _ h0
    have hlt1 : 2 * i < D.R.m := by omega
    have hlt2 : 2 * i + 1 < D.R.m := by omega
    have h2 := stepK t hK (j := 2 * i + 1) hlt2 (hI.stabK (2 * i) hlt1 _ hS) (hI.stabK (2 * i) hlt1 _ hw) _ h1
    refine ⟨hI.stabK (2 * i + 1) hlt2 _ (hI.stabK (2 * i) hlt1 _ hS), fun α y => ?_⟩
    have hc : o.cS (i + 1) = o.cS i * ∏ l ∈ Finset.range (2 * i), o.cL l := by
      simp only [TDat.cS, Finset.prod_range_succ]
    rw [hc]
    exact h2 α y

end GlobalTheory.SeeSaw.MoveZero

namespace GlobalTheory.SeeSaw

theorem commX_of_laws : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ)
    (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0),
    t.Is → t.KBack → t.TailRd → LiftS o t → ReadS o t ε S₀ → CommX o t ε S₀ := by
  intro D c k _ _ _ _ ι o t ε S₀ hI hK hT hL hR n h ψ hψ F
  obtain ⟨hu, hr⟩ := MoveZero.stepC o t ε S₀ hI hK hL hR n h.le ψ hψ
  exact hT (2 * n) h _ hu _ (MoveZero.col_mem t hI (2 * n) h.le _ (MoveZero.iterS_mem o t ε S₀ hR n ψ hψ)) _ hr F

end GlobalTheory.SeeSaw
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZeroStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0), t.Is → t.KBack → t.TailRd → LiftS o t → ReadS o t ε S₀ → CommX o t ε S₀ := by
  first | exact @GlobalTheory.SeeSaw.commX_of_laws | exact GlobalTheory.SeeSaw.commX_of_laws | (intros; apply GlobalTheory.SeeSaw.commX_of_laws <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.AdForm GlobalTheory.AdForm.RdVal
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MiTop.LComm

variable {D : D7}

theorem exists_finM (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (y : Formalism.UG.UPts (Formalism.L2.Forms.sigD D) (V.gram.reindex (finCongr hn) (finCongr hn))
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    ∃ a : GA D V, GlobalTheory.AdForm.finM V hn a = y.1.1 := by
  subst hn
  obtain ⟨a, -, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V ⟨y.1, y.2⟩
  refine ⟨a, ?_⟩
  have e2 := congrArg Subtype.val e
  have e3 := congrArg Units.val e2
  exact e3


set_option maxHeartbeats 2000000 in
theorem rdS_inj (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
    (yc : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hbij : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S)))
    (ψ ψ' : cl → Frames (gramC (V.gram.reindex (finCongr hn) (finCongr hn)) (embT D)) → ℂ)
    (h : ∀ y, rdS θ V hn S yc ψ y = rdS θ V hn S yc ψ' y) : ψ = ψ' := by
  funext c z
  obtain ⟨g, hg⟩ := exists_finM V hn (yc c)
  have hex : ∃ p, IsDec S yc (finM V hn g) p := by
    refine ⟨(c, 1, 1), Subgroup.one_mem _, ?_⟩
    simp [hg]
  have hp := hex.choose_spec
  have hc : hex.choose.1 = c := by
    apply hbij.1
    refine (@DoubleCoset.eq _ _ _ _ _ _).mpr ?_
    have hr : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        ratPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      Subgroup.mem_map.mpr ⟨_, hp.1, rfl⟩
    have hk : hex.choose.2.2.1 ∈ UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
      ((S.U_eq _).1 hex.choose.2.2.2).1
    have he : (yc c).1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 * (yc hex.choose.1).1 *
        hex.choose.2.2.1 := Units.ext (hg.symm.trans hp.2)
    have hγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      have : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) hex.choose.2.1 =
          (yc c).1 * (hex.choose.2.2.1)⁻¹ * ((yc hex.choose.1).1)⁻¹ := by rw [he]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (yc c).2 (Subgroup.inv_mem _ hk)) (Subgroup.inv_mem _ (yc _).2)
    exact ⟨⟨_, hγ⟩, Subgroup.mem_subgroupOf.mpr hr, ⟨_, hk⟩, Subgroup.mem_subgroupOf.mpr hex.choose.2.2.2, Subtype.ext he⟩
  set A : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ := fun τ =>
    atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ with hA
  have hAu : ∀ τ, IsUnit (A τ).det := by
    intro τ
    rw [hA, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (atInf_mul_inv hex.choose.2.1 τ)).mul (infM_unit θ V hn g τ)
  have hy : ∀ τ, IsUnit ((A τ)⁻¹ * z.1 τ).det := by
    intro τ
    rw [Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det _ (hAu τ)).mul (z.2 τ)
  have key := congrFun (h ⟨fun τ => (A τ)⁻¹ * z.1 τ, hy⟩) g
  have hz : (fun τ => atInf (embT D) ((hex.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * ((A τ)⁻¹ * z.1 τ)) = z.1 := by
    funext τ
    show A τ * ((A τ)⁻¹ * z.1 τ) = _
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hAu τ), Matrix.one_mul]
  unfold rdS at key
  rw [dite_eq_left hex, dite_eq_left hex] at key
  dsimp only at key
  rw [hz, atFr, atFr, dite_eq_left z.2, dite_eq_left z.2, hc] at key
  exact mul_left_cancel₀ (Units.ne_zero _) key

theorem chart0_inj {u : D.what₂.Word} (F : Forms0 D u) (θ : InfFam D) (ψ ψ' : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)
    (h : ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ ψ y = (GlobalTheory.Core.Mi.chart0 F).rd θ ψ' y) : ψ = ψ' := by
  have := rdS_inj θ (D.sp.X 0) (rankN D 0 (Nat.zero_le _)) F.cls0.lev F.cls0.y F.cls0.y_bij
    (fun c z => ψ c (F.val0.eY.symm z)) (fun c z => ψ' c (F.val0.eY.symm z)) (fun y => by
      have := h (F.val0.eY.symm y)
      unfold Chart.rd at this
      rw [show (GlobalTheory.Core.Mi.chart0 F).eY (F.val0.eY.symm y) = y from F.val0.eY.apply_symm_apply y] at this
      exact this)
  funext c y
  have h2 := congrFun (congrFun this c) (F.val0.eY y)
  simpa using h2

theorem iter_equiv {M β : Type} [NormedAddCommGroup M] [Module ℂ M] (S : β → M ≃ₗ[ℂ] M) (r : β → ℝ) (hr : ∀ b, 0 < r b)
    (hS : ∀ b φ, ‖S b φ‖ = r b * ‖φ‖) (ε : ℕ → β) (n : ℕ) :
    ∃ (A : M ≃ₗ[ℂ] M) (a : ℝ), 0 < a ∧ (∀ φ, ‖A φ‖ = a * ‖φ‖) ∧ ∀ φ, A φ = GlobalTheory.SeeSaw.iterS (fun b => S b) ε n φ := by
  induction n with
  | zero => exact ⟨LinearEquiv.refl ℂ M, 1, one_pos, fun φ => by simp, fun φ => rfl⟩
  | succ n ih =>
    obtain ⟨A, a, ha, h1, h2⟩ := ih
    refine ⟨A.trans (S (ε (2 * n))), r (ε (2 * n)) * a, mul_pos (hr _) ha, fun φ => ?_, fun φ => ?_⟩
    · rw [LinearEquiv.trans_apply, hS, h1, mul_assoc]
    · rw [LinearEquiv.trans_apply, h2]; rfl

theorem iterS_comm {α α' β : Type} (S : β → α → α) (S' : β → α' → α') (j : α → α') (h : ∀ b x, S' b (j x) = j (S b x))
    (ε : ℕ → β) (n : ℕ) (x : α) : GlobalTheory.SeeSaw.iterS S' ε n (j x) = j (GlobalTheory.SeeSaw.iterS S ε n x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show S' _ (GlobalTheory.SeeSaw.iterS S' ε n (j x)) = j (S _ (GlobalTheory.SeeSaw.iterS S ε n x))
    rw [ih, h]

end GlobalTheory.MiTop.LComm
end

open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl
