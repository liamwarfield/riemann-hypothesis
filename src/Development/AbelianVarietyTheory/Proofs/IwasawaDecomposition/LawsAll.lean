module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteOrbitsOfFiniteFibres
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFock

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkAlt
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.LRank


open scoped TensorProduct in
theorem natCard_quot {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Projective R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv, Nat.card_congr b.equivFun.toEquiv,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (p : Submodule (𝓞 K) V)
    (h : Submodule.span K (p : Set V) = ⊤) : Module.finrank (𝓞 K) p = Module.finrank K V := by
  have : IsLocalizedModule (nonZeroDivisors (𝓞 K)) p.subtype := by
    refine ⟨fun s => ?_, fun y => ?_, fun {a b} hab => ⟨1, by simpa using hab⟩⟩
    · have := isLocalizedModule_id (nonZeroDivisors (𝓞 K)) V K
      exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 K)) (LinearMap.id : V →ₗ[𝓞 K] V) s
    · have hy : y ∈ Submodule.span K (p : Set V) := h ▸ Submodule.mem_top
      obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 K)) K _ y hy
      rw [Submodule.span_eq] at ht
      exact ⟨(⟨_, ht⟩, t), rfl⟩
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (𝓞 K)) p.subtype le_rfl,
    IsFractionRing.finrank_right_eq (𝓞 K) K V]

theorem finrank_of_card {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] {n : ℕ}
    (h : Nat.card V = Nat.card F ^ n) : Module.finrank F V = n := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have : Module.Finite F V := Module.Finite.of_finite
  have h2 := Module.natCard_eq_pow_finrank (K := F) (V := V)
  rw [h] at h2
  exact (Nat.pow_right_injective h1 h2).symm


set_option maxHeartbeats 800000 in
theorem finrank_red {E : Type} [Field E] [NumberField E] {n : ℕ} (N : Submodule (𝓞 E) (Fin n → E))
    (hN : Submodule.IsFullLattice E N) (P : HeightOneSpectrum (𝓞 E)) :
    Module.finrank (Res P) (TDat.Red N P) = n := by
  let : Submodule.IsFullLattice E N := hN
  have : Module.Finite (𝓞 E) N := Submodule.IsLattice.finite E N
  have : Module.FinitePresentation (𝓞 E) N := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 E) N := inferInstance
  have : Module.Projective (𝓞 E) N := Module.Flat.projective_of_finitePresentation
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  have hr : Module.finrank (𝓞 E) N = n := by
    exact (Submodule.IsFullLattice.finrank_eq E N).trans (Module.finrank_fin_fun E)
  have h := natCard_quot (R := 𝓞 E) (N := N) P.asIdeal
  rw [hr] at h
  exact finrank_of_card (F := Res P) h


set_option maxHeartbeats 1600000 in
theorem ranks : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  intro E K _ _ _ _ n S ST A T _ h
  exact ⟨fun P c => finrank_red _ (h.N_lat c.1 (S.rep c)) P.1,
    fun P c => finrank_red _ (h.dnN_lat c.1 (S.rep c) P) P.1⟩

end GlobalTheory.Mem.Col2.LRank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeLevelStructureDataRanksModPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primeLevelStructureData_ranks_mod_prime : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, Module.finrank (Res P.1) (A.lv P c) = n) ∧ ∀ P c, Module.finrank (Res P.1) (A.lk P c) = n := by
  first | exact @GlobalTheory.Mem.Col2.LRank.ranks | exact GlobalTheory.Mem.Col2.LRank.ranks | (intros; apply GlobalTheory.Mem.Col2.LRank.ranks <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClasses
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClasses
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaCl

variable {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {S : GStep E K n}
  {ST : Finset (HeightOneSpectrum (𝓞 E))} {A : TDat S ST} {T : ℕ}

theorem cl_smul_eq (b : S.β) (g : S.G b) (d : S.D b) : S.cl b (g • d) = S.cl b d :=
  congrArg (Sigma.mk b) (Quotient.sound (show (MulAction.orbitRel (S.G b) (S.D b)).r (g • d) d from ⟨g, rfl⟩))

theorem cl_rep_eq (c : S.Cl) : S.cl c.1 (S.rep c) = c := by
  obtain ⟨b, q⟩ := c
  exact congrArg (Sigma.mk b) (S.rp_spec b q)

theorem exists_move (b : S.β) (d : S.D b) : ∃ g : S.G b, g • S.rep (S.cl b d) = d :=
  (MulAction.orbitRel (S.G b) (S.D b)).symm (Quotient.exact (S.rp_spec b (Quotient.mk _ d)))

theorem dia_inj (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) : Function.Injective (A.dia b P a) := by
  intro d d' hd
  have := congrArg (A.dia b P a⁻¹) hd
  rwa [← h.dia_mul, ← h.dia_mul, inv_mul_cancel, h.dia_one, h.dia_one] at this

theorem stab_dia (h : A.Ok T) (b : S.β) (P : ST) (a : (Res P.1)ˣ) (d : S.D b) :
    MulAction.stabilizer (S.G b) (A.dia b P a d) = MulAction.stabilizer (S.G b) d := by
  ext g
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← h.dia_act]
  exact (dia_inj h b P a).eq_iff

theorem card_stab_cl (b : S.β) (d : S.D b) :
    Nat.card (S.Stab (S.cl b d)) = Nat.card (MulAction.stabilizer (S.G b) d) := by
  obtain ⟨g, hg⟩ := exists_move (S := S) b d
  exact Nat.card_congr (MulAction.stabilizerEquivStabilizer hg.symm).toEquiv

end GlobalTheory.Mem.Col2.DiaCl

namespace GlobalTheory.Mem.Col2

open DiaCl

theorem diamond_action_on_classes : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T →
    (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧
    (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧
    ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  intro E K _ _ _ _ n S ST A T _ h
  refine ⟨fun P c => ?_, fun P a b c => ?_, fun P a c => ?_⟩
  · unfold TDat.diaPt
    rw [h.dia_one, cl_rep_eq]
  · unfold TDat.diaPt
    obtain ⟨g, hg⟩ := exists_move (S := S) c.1 (A.dia c.1 P b (S.rep c))
    rw [← cl_smul_eq c.1 g (A.dia c.1 P a _), ← h.dia_act, hg, h.dia_mul]
  · rw [card_stab_cl]
    unfold TDat.diaPt
    rw [stab_dia h]

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiamondActionOnHermitianChartClassesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_action_on_hermitianChartClasses : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → (∀ P c, S.cl c.1 (A.diaPt P 1 c) = c) ∧ (∀ P a b c, S.cl c.1 (A.diaPt P (a * b) c) = S.cl c.1 (A.diaPt P a (S.cl c.1 (A.diaPt P b c)))) ∧ ∀ P a c, Nat.card (S.Stab (S.cl c.1 (A.diaPt P a c))) = Nat.card (S.Stab c) := by
  first | exact @GlobalTheory.Mem.Col2.diamond_action_on_classes | exact GlobalTheory.Mem.Col2.diamond_action_on_classes | (intros; apply GlobalTheory.Mem.Col2.diamond_action_on_classes <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2


set_option maxHeartbeats 1600000 in
theorem TDat.laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  intro E K _ _ _ _ n S ST A T hS hA
  have h1 := GlobalTheory.T.primeLevelStructureData_ranks_mod_prime A T hS hA
  have h2 := GlobalTheory.T.levelFunctional_levelVector_laws A T hS hA
  have h3 := GlobalTheory.T.diamond_action_on_hermitianChartClasses A T hS hA
  have h4 := GlobalTheory.T.levelFunctional_dilated_class A T hS hA
  exact ⟨h1.1, h1.2, h2.2.1, h2.2.2, h3.1, h3.2.1, h4, h3.2.2⟩

end GlobalTheory.Mem.Col2
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tDat_laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n} {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  first | exact @GlobalTheory.Mem.Col2.TDat.laws_of_ok | exact GlobalTheory.Mem.Col2.TDat.laws_of_ok | (intros; apply GlobalTheory.Mem.Col2.TDat.laws_of_ok <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralForms
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralForms
namespace GlobalTheory.Mem.Col2.DiaLat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem evV_rho_tr (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem exists_pull (hf : S.Free) (h : (S.fam emb lam).Ok) (p : ∀ c : S.Cl, S.D c.1)
    (hp : ∀ c, S.Lsh c.1 (p c) = S.Lsh c.1 (S.rep c)) (x : S.FormsK emb lam h) (hx : x ∈ (S.hlat emb lam h).L) :
    ∃ y ∈ (S.hlat emb lam h).L, ∀ c, S.embF emb σ lam h y c =
      S.trTo emb σ c.1 (p c) (S.embF emb σ lam h x (S.cl c.1 (p c))) := by
  refine ⟨⟨fun c => S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))), fun c g => ?_⟩, fun c => ?_, fun c => ?_⟩
  · have hg : (g.1 : S.G c.1) = 1 := hf c.1 g.1 (S.rep c) g.2
    show S.rho emb lam c.1 g.1 _ = _
    rw [hg, map_one]
    rfl
  · have h1 : delAtr emb lam (S.Lsh c.1 (S.mv c.1 (p c) • S.rep (S.cl c.1 (p c)))) =
        (delAtr emb lam (S.Lsh c.1 (S.rep (S.cl c.1 (p c))))).map
          ((S.rho emb lam c.1 (S.mv c.1 (p c))).restrictScalars (𝓞 K)) :=
      (h c.1).del_smul (S.mv c.1 (p c)) (S.rep (S.cl c.1 (p c)))
    rw [S.mv_smul, hp] at h1
    show S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))) ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))
    rw [h1]
    exact Submodule.mem_map_of_mem (hx (S.cl c.1 (p c)))
  · exact evV_rho_tr S emb σ lam c.1 _ _

end General

theorem dia_lat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ hJ hF P a x hx
  obtain ⟨y, hy, e⟩ := exists_pull (I.S 0) emb σ (lamT hc 0) hJ.free0 hF (fun c => (J.A 0).diaPt P a c)
    (fun c => (hJ.lev 0).dia_Lsh c.1 P a _) x hx
  exact ⟨y, hy, funext e⟩

end GlobalTheory.Mem.Col2.DiaLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralFormsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_integralForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  first | exact @GlobalTheory.Mem.Col2.DiaLat.dia_lat | exact GlobalTheory.Mem.Col2.DiaLat.dia_lat | (intros; apply GlobalTheory.Mem.Col2.DiaLat.dia_lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMem
namespace GlobalTheory.NonzeroSmulMem

open NumberField

theorem exists_ne_zero_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]
      exact M.smul_mem b hay
    · rw [mul_smul]
      exact M.smul_mem a hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨p, q, hq, hc⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqK : algebraMap (𝓞 K) K q ≠ 0 := by
      intro h
      exact hq0 ((IsFractionRing.injective (𝓞 K) K) (by rw [h, map_zero]))
    refine ⟨a * q, mul_ne_zero ha hq0, ?_⟩
    have h1 : q • (c • y) = p • y := by
      rw [← algebraMap_smul K q, ← algebraMap_smul K p, smul_smul, ← hc,
        mul_div_cancel₀ _ hqK]
    rw [mul_smul, h1, smul_smul, mul_comm, mul_smul]
    exact M.smul_mem p hay

end GlobalTheory.NonzeroSmulMem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.BSpan

theorem exists_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMem.exists_ne_zero_smul_mem ..)

theorem smul_mem_of_dvd {A V : Type} [CommRing A] [AddCommGroup V] [Module A V] {M : Submodule A V} {a b : A} {x : V}
    (hab : a ∣ b) (hx : a • x ∈ M) : b • x ∈ M := by
  obtain ⟨c, rfl⟩ := hab
  rw [mul_comm, mul_smul]
  exact M.smul_mem _ hx

theorem dualFr_isFullLattice {K : Type} [Field K] [NumberField K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K))
    (hM : Submodule.IsFullLattice K M) : Submodule.IsFullLattice K (dualFr M) :=
  GlobalTheory.DualLat.isLattice_dualFr M hM


theorem isLattice_delAtr {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] {n : ℕ}
    (emb : ι → E →+* K) (lam : ι → DomWeight n) (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsFullLattice E L) :
    Submodule.IsFullLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    dualFr_isFullLattice _ (GlobalTheory.TauLat.tauLat_lattice_dual_round.1 E K ι n emb τ L hL)).2

theorem span_locW_eq_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (Pl : Rows.Places K) (w : Pl.Pl) (M : Submodule (𝓞 K) V)
    (h : ∀ x : V, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M) : Submodule.span K (locW Pl w M : Set V) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨d, hd, hx⟩ := h x
  have hd' : algebraMap (𝓞 K) K d ≠ 0 := by simpa using hd
  have : x = (algebraMap (𝓞 K) K d)⁻¹ • (d • x) := by
    rw [← algebraMap_smul K d x, smul_smul, inv_mul_cancel₀ hd', one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span hx))

theorem exists_smul_mem_latOf {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok)
    [Finite S.Cl] (M : S.Cl → Submodule (𝓞 K) (VV K lam)) (hM : ∀ c, Submodule.span K (M c : Set (VV K lam)) = ⊤)
    (x : S.FormsK emb lam h) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ S.latOf emb lam h M := by
  classical
  haveI := Fintype.ofFinite S.Cl
  have h1 : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c => exists_smul_mem (by rw [hM c]; trivial)
  choose d hd hdM using h1
  refine ⟨∏ c, d c, Finset.prod_ne_zero_iff.2 fun c _ => hd c, fun c => ?_⟩
  exact smul_mem_of_dvd (Finset.dvd_prod_of_mem d (Finset.mem_univ c)) (hdM c)


set_option maxHeartbeats 800000 in
theorem span_locW_BLat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Pl : Rows.Places K) i (hF : ((I.S i).fam emb (lamT hc i)).Ok) (w : Pl.Pl) P, Submodule.span K (locW Pl w (BLat J emb hc i hF P) : Set ((I.S i).hlat emb (lamT hc i) hF).V) = ⊤ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ hI hJ Pl i hF w P
  haveI := (hI.step i).fin_orb
  refine span_locW_eq_top Pl w _ fun x => ?_
  exact exists_smul_mem_latOf (I.S i) emb (lamT hc i) hF _
    (fun c => by
      let b := c.1
      let d := (I.S i).rep c
      have hd := (hJ.tied i).ok b d
      have hker : Submodule.IsFullLattice E ((J.A i).ker b d P) := by
        letI := (hJ.lev i).ker_lat b d P
        letI := (hJ.lev i).N_lat b d
        refine { span_eq_top := top_unique ?_ }
        rw [← (Submodule.IsFullLattice.span_eq_top (A := E) (M := (J.A i).N b d)), Submodule.span_le]
        intro x hx
        obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot P.1.ne_bot
        have hrx : r • x ∈ (J.A i).ker b d P := by
          rw [(hJ.tied i).ker_eq]
          exact Submodule.subset_span ⟨hd.N_le_Lsh (Submodule.smul_mem _ r hx),
            ((hd.mem_kerAt P _).1 (hd.smul_mem_kerAt P hr hx)).2⟩
        have hrE : algebraMap (𝓞 E) E r ≠ 0 := by simpa using hr0
        have hspan : r • x ∈ Submodule.span E (((J.A i).ker b d P) : Set _) :=
          Submodule.subset_span hrx
        have hh : (algebraMap (𝓞 E) E r)⁻¹ • (r • x) ∈
            Submodule.span E (((J.A i).ker b d P) : Set _) := Submodule.smul_mem _ _ hspan
        rw [← algebraMap_smul E r x, smul_smul, inv_mul_cancel₀ hrE, one_smul] at hh
        exact hh
      letI := isLattice_delAtr emb (lamT hc i) ((J.A i).ker b d P) hker
      exact Submodule.IsFullLattice.span_eq_top) x

end GlobalTheory.Mem.BSpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_span_at_place : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Pl : Rows.Places K) i (hF : ((I.S i).fam emb (lamT hc i)).Ok) (w : Pl.Pl) P, Submodule.span K (locW Pl w (BLat J emb hc i hF P) : Set ((I.S i).hlat emb (lamT hc i) hF).V) = ⊤ := by
  first | exact @GlobalTheory.Mem.BSpan.span_locW_BLat | exact GlobalTheory.Mem.BSpan.span_locW_BLat | (intros; apply GlobalTheory.Mem.BSpan.span_locW_BLat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentation
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2.DiaRep

set_option linter.unusedSectionVars false

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem trFr_mul_apply (γ δ : GL (Fin n) E) (c d : Kˣ) (F : Fr emb σ n → ℂ) :
    trFr emb σ (γ * δ) (c * d) F = trFr emb σ γ c (trFr emb σ δ d F) := by
  funext y
  simp only [trFr_apply, mul_inv_rev, frMul_mul, Units.val_mul, map_mul, mul_assoc]

theorem trFr_one_apply (F : Fr emb σ n → ℂ) : trFr emb σ (1 : GL (Fin n) E) (1 : Kˣ) F = F := by
  funext y
  simp only [trFr_apply, inv_one, frMul_one, Units.val_one, map_one, one_mul]

theorem tr_mul_apply (b : S.β) (g h : S.G b) (F : Fr emb σ n → ℂ) :
    S.tr emb σ b (g * h) F = S.tr emb σ b g (S.tr emb σ b h F) := by
  unfold GStep.tr
  rw [map_mul, map_mul, trFr_mul_apply]

theorem tr_one_apply (b : S.β) (F : Fr emb σ n → ℂ) : S.tr emb σ b 1 F = F := by
  unfold GStep.tr
  rw [map_one, map_one, trFr_one_apply]

theorem mk_smul (b : S.β) (g : S.G b) (d : S.D b) :
    Quotient.mk (MulAction.orbitRel (S.G b) (S.D b)) (g • d) = Quotient.mk _ d :=
  Quotient.sound ⟨g, rfl⟩

theorem mv_smul' (b : S.β) (d : S.D b) : S.mv b d • S.rp b (Quotient.mk _ d) = d := S.mv_smul b d

theorem eq_of_free (hf : S.Free) (b : S.β) (g h : S.G b) (d : S.D b) (e : g • d = h • d) : g = h := by
  have h1 : (h⁻¹ * g) • d = d := by rw [mul_smul, e, inv_smul_smul]
  have h2 := hf b _ d h1
  exact (inv_mul_eq_one.1 h2).symm

theorem mv_smul_eq (hf : S.Free) (b : S.β) (g : S.G b) (d : S.D b) : S.mv b (g • d) = g * S.mv b d := by
  apply eq_of_free S hf b _ _ (S.rp b (Quotient.mk _ d))
  have h1 := mv_smul' S b (g • d)
  rw [mk_smul] at h1
  rw [h1, mul_smul, mv_smul']

theorem mv_rp (hf : S.Free) (b : S.β) (q : MulAction.orbitRel.Quotient (S.G b) (S.D b)) : S.mv b (S.rp b q) = 1 := by
  apply hf b _ (S.rp b q)
  have h1 := mv_smul' S b (S.rp b q)
  rwa [S.rp_spec] at h1

def evPt (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (d : S.D b) : Fr emb σ n → ℂ :=
  S.tr emb σ b (S.mv b d) (φ ⟨b, Quotient.mk _ d⟩)

theorem evPt_smul (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (b : S.β) (g : S.G b) (d : S.D b) :
    evPt S emb σ φ b (g • d) = S.tr emb σ b g (evPt S emb σ φ b d) := by
  unfold evPt
  rw [mv_smul_eq S hf, tr_mul_apply, mk_smul]

theorem evPt_rep (hf : S.Free) (φ : S.Cl → Fr emb σ n → ℂ) (c : S.Cl) :
    evPt S emb σ φ c.1 (S.rep c) = φ c := by
  obtain ⟨b, q⟩ := c
  show S.tr emb σ b (S.mv b (S.rp b q)) (φ ⟨b, Quotient.mk _ (S.rp b q)⟩) = φ ⟨b, q⟩
  rw [mv_rp S hf, tr_one_apply, S.rp_spec]

end Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks}
  {I : ChainIn E K ι R} (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ)

theorem diaLin_apply (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ) (c : (I.S 0).Cl) :
    J.diaLin emb σ P a φ c = evPt (I.S 0) emb σ φ c.1 ((J.A 0).dia c.1 P a ((I.S 0).rep c)) := rfl

theorem evPt_diaLin (h : J.Ok) (P : J.ST) (a : (Res P.1)ˣ) (φ : (I.S 0).Cl → Fr emb σ (R.N 0) → ℂ)
    (b : (I.S 0).β) (d : (I.S 0).D b) :
    evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a d) := by
  have h1 : evPt (I.S 0) emb σ (J.diaLin emb σ P a φ) b d = (I.S 0).tr emb σ b ((I.S 0).mv b d)
      (evPt (I.S 0) emb σ φ b ((J.A 0).dia b P a ((I.S 0).rp b (Quotient.mk _ d)))) := rfl
  rw [h1, ← evPt_smul _ _ _ h.free0, ← (h.lev 0).dia_act, mv_smul']

theorem lawDiaOne (h : J.Ok) : J.LawDiaOne emb σ := by
  intro P
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [diaLin_apply, (h.lev 0).dia_one, evPt_rep _ _ _ h.free0]
  rfl

theorem lawDiaMul (h : J.Ok) : J.LawDiaMul emb σ := by
  intro P a b
  refine LinearMap.ext fun φ => funext fun c => ?_
  rw [Module.End.mul_apply, diaLin_apply, diaLin_apply, evPt_diaLin J emb σ h, ← (h.lev 0).dia_mul, mul_comm b a]

theorem diamond_rep : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K]
    [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R),
    FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ :=
  fun _ J emb σ _ _ _ h => ⟨lawDiaOne J emb σ h, lawDiaMul J emb σ h⟩

end GlobalTheory.Mem.Col2.DiaRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimeDiamond_representation : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaOne emb σ ∧ J.LawDiaMul emb σ := by
  first | exact @GlobalTheory.Mem.Col2.DiaRep.diamond_rep | exact GlobalTheory.Mem.Col2.DiaRep.diamond_rep | (intros; apply GlobalTheory.Mem.Col2.DiaRep.diamond_rep <;> assumption)
end
end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2


set_option maxHeartbeats 1600000 in
theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := GlobalTheory.T.levelPrimeDiamond_representation I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => GlobalTheory.T.hermitianLatticeChartFamily_fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := GlobalTheory.T.hermitianLatticeChartFamily_fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => GlobalTheory.T.tDat_laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => GlobalTheory.T.weight_law_good_of_field_embedding (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => GlobalTheory.T.hermitianLatticeChartFamily_lawBasis (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; GlobalTheory.T.lawNorm_classSum_fock (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := GlobalTheory.T.weight_law_good_of_field_embedding Q.S' emb σ Q.sgT hF hQ.step _
      basisP := GlobalTheory.T.hermitianLatticeChartFamily_lawBasis Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; GlobalTheory.T.lawNorm_classSum_fock Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := GlobalTheory.T.levelPrimeDiamond_preserves_integralForms I J emb σ hc hF hI hJ _
      B_span := fun i w P => GlobalTheory.T.local_lattice_span_at_place I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
