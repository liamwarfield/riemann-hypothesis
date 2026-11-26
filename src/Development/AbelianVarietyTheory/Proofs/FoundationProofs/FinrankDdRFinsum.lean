module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerCrystallineCocycles
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankDdRFinsum
noncomputable section

namespace GlobalTheory.DeRhamSplit

open Module TensorProduct

section General

variable {F K L M : Type} [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
  [AddCommGroup M] [Module L M] [Module F M] [IsScalarTower F L M]

def evalEmb (F K L : Type) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] :
    L ⊗[F] K →ₐ[L] ((K →ₐ[F] L) → L) :=
  Algebra.TensorProduct.lift (Algebra.ofId L _) (AlgHom.pi fun τ => τ) fun _ _ => .all _ _

theorem evalEmb_tmul (a : L) (c : K) (τ : K →ₐ[F] L) :
    evalEmb F K L (a ⊗ₜ c) τ = a * τ c := by
  simp [evalEmb, Algebra.ofId_apply]

theorem evalEmb_bijective [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) : Function.Bijective (evalEmb F K L) := by
  have hli : LinearIndependent L (fun τ : K →ₐ[F] L => (τ : K → L)) := by
    have h := (linearIndependent_monoidHom K L).comp (fun τ : K →ₐ[F] L => (τ : K →* L))
      (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    exact h
  have hspan := span_flip_eq_top_iff_linearIndependent.2 hli
  have hsurj : Function.Surjective (evalEmb F K L).toLinearMap := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨c, rfl⟩
    refine ⟨1 ⊗ₜ c, ?_⟩
    funext τ
    simp [evalEmb_tmul, flip]
  have hfin : finrank L (L ⊗[F] K) = finrank L ((K →ₐ[F] L) → L) := by
    simp [hcard]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj, hsurj⟩

theorem finrank_eq_sum [FiniteDimensional F K]
    (hcard : Fintype.card (K →ₐ[F] L) = finrank F K) (m : K →ₐ[F] Module.End L M)
    (W : Submodule L M) [FiniteDimensional L W] (hW : ∀ c, ∀ x ∈ W, m c x ∈ W) :
    finrank L W = ∑ τ : K →ₐ[F] L,
      finrank L ↥(W ⊓ ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)) := by
  classical
  have hcomm : ∀ (a : L) (c : K), Commute (Algebra.ofId L (Module.End L M) a) (m c) :=
    fun a c => Algebra.commutes a (m c)
  let Ψ : L ⊗[F] K →ₐ[L] Module.End L M :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) m hcomm
  have hΨ : ∀ a c x, Ψ (a ⊗ₜ c) x = a • m c x := by
    intro a c x
    change (Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ c) : Module.End L M) x = _
    rw [Algebra.TensorProduct.lift_tmul]
    simp [Algebra.ofId_apply]
  let Φ := AlgEquiv.ofBijective _ (evalEmb_bijective hcard)
  let e : (K →ₐ[F] L) → L ⊗[F] K := fun τ => Φ.symm (Pi.single τ 1)
  have he : ∀ τ, evalEmb F K L (e τ) = Pi.single τ 1 := fun τ => Φ.apply_symm_apply _
  let E : (K →ₐ[F] L) → Submodule L M := fun τ => ⨅ c : K, LinearMap.ker (m c - τ c • LinearMap.id)
  have hE : ∀ τ x, x ∈ E τ ↔ ∀ c, m c x = τ c • x := by
    intro τ x
    simp [E, Submodule.mem_iInf, sub_eq_zero]
  have hΨW : ∀ z, ∀ x ∈ W, Ψ z x ∈ W := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact W.smul_mem _ (hW c x hx)
    | add y z hy hz => rw [map_add (f := _)]; exact W.add_mem hy hz
  have hΨE : ∀ σ, ∀ x ∈ E σ, ∀ z, Ψ z x = evalEmb F K L z σ • x := by
    intro σ x hx z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, evalEmb_tmul, (hE σ x).1 hx, mul_smul]
    | add y z hy hz => simp [map_add (f := _), hy, hz, add_smul]
  have hsum : ∑ τ, e τ = 1 := by
    apply (evalEmb_bijective hcard).1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : L))
  have hmul : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := by
    intro τ c
    apply (evalEmb_bijective hcard).1
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [evalEmb_tmul]
    · simp [Pi.single_eq_of_ne h]
  have hpE : ∀ τ x, Ψ (e τ) x ∈ E τ := by
    intro τ x
    rw [hE]
    intro c
    have := congrArg (fun z => Ψ z x) (hmul τ c)
    simpa [map_mul, map_smul, hΨ] using this
  let f : W →ₗ[L] (∀ τ, ↥(W ⊓ E τ)) := LinearMap.pi fun τ =>
    LinearMap.codRestrict _ ((Ψ (e τ)) ∘ₗ W.subtype) fun x => ⟨hΨW _ _ x.2, hpE τ _⟩
  have hf : ∀ x τ, (f x τ : M) = Ψ (e τ) x := fun _ _ => rfl
  have hbij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro x hx
      have h1 : (x : M) = ∑ τ, Ψ (e τ) x := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← LinearMap.sum_apply, ← map_sum, hsum, map_one]; rfl
      apply Subtype.ext
      rw [h1]
      simp [← hf, hx]
    · intro y
      refine ⟨⟨∑ σ, (y σ : M), W.sum_mem fun σ _ => (y σ).2.1⟩, ?_⟩
      funext τ
      apply Subtype.ext
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf, map_sum, Finset.sum_eq_single τ]
      · rw [hΨE τ _ (y τ).2.2, he]; simp
      · intro σ _ h
        rw [hΨE σ _ (y σ).2.2, he]; simp [Pi.single_eq_of_ne h]
      · simp
  have : ∀ τ, FiniteDimensional L ↥(W ⊓ E τ) := fun τ =>
    Submodule.finiteDimensional_of_le inf_le_left
  rw [(LinearEquiv.ofBijective f hbij).finrank_eq, Module.finrank_pi_fintype]

end General

section Period

open Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mulVdR_tmul (c : K) (v : V) (b : BdR) :
    mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c (v ⊗ₜ[Qp] b) =
      v ⊗ₜ[Qp] (algebraMap K BdR c * b) := by
  simp [mulVdR]

def mulHom (Qp K BdR LL V : Type) [Field Qp] [Field K] [Algebra Qp K] [CommRing BdR]
    [Algebra Qp BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [Field LL] [Algebra Qp LL]
    [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] :
    K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) where
  toFun c := mulVdR (Qp := Qp) (K := K) (BdR := BdR) (V := V) (LL := LL) c
  map_one' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_mul' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, mul_assoc]
  map_zero' := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul]
  map_add' c d := by
    apply AlgebraTensorModule.ext
    intro v b
    simp [mulVdR_tmul, add_mul, tmul_add]
  commutes' a := by
    apply AlgebraTensorModule.ext
    intro v b
    rw [mulVdR_tmul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, tmul_smul]
    simp [Algebra.algebraMap_eq_smul_one]

theorem act_mul (g : G) (c : K) (x : V ⊗[Qp] BdR) :
    actVdR PD ρ g (mulVdR (K := K) (LL := LL) c x) = mulVdR (K := K) (LL := LL) c (actVdR PD ρ g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR, mulVdR_tmul]
  | add y z hy hz => simp [map_add (f := _), hy, hz]

theorem mul_mem_DdR (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ DdR PD ρ) :
    mulVdR (K := K) (LL := LL) c x ∈ DdR PD ρ := by
  simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx ⊢
  intro g
  rw [act_mul, hx]

theorem mul_mem_FilV (a : ℤ) (c : K) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    mulVdR (K := K) (LL := LL) c x ∈ FilV PD (LL := LL) (V := V) a := by
  obtain ⟨y, rfl⟩ := hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    refine ⟨v ⊗ₜ ⟨c • b.1, (PD.Fil a).smul_mem c b.2⟩, ?_⟩
    simp [mulVdR_tmul, Algebra.smul_def]
  | add y z hy hz => rw [map_add (f := _), map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem finrank_DdR [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  refine ⟨finrank_eq_sum hcard (mulHom Qp K BdR LL V) _ (mul_mem_DdR PD ρ), ?_⟩
  have : FiniteDimensional LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) :=
    Submodule.finiteDimensional_of_le inf_le_left
  rw [finrank_eq_sum hcard (mulHom Qp K BdR LL V) (DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a)
    (fun c x hx => ⟨mul_mem_DdR PD ρ c x hx.1, mul_mem_FilV PD a c x hx.2⟩)]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [inf_right_comm]
  rfl

theorem finrank_DdR_finsum [FiniteDimensional Qp K] (hcard : Nat.card (K →ₐ[Qp] LL) = finrank Qp K)
    [FiniteDimensional LL ↥(DdR PD ρ)] (a : ℤ) :
    finrank LL ↥(DdR PD ρ) = ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(DdRE PD ρ τ) ∧
    finrank LL ↥(DdR PD ρ ⊓ FilV PD (LL := LL) (V := V) a) =
      ∑ᶠ τ : K →ₐ[Qp] LL, finrank LL ↥(FildR PD ρ τ a) := by
  rw [Nat.card_eq_fintype_card] at hcard
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  exact finrank_DdR PD ρ hcard a

end Period

open Formalism.BasicNotions in
theorem card_emb {l : ℕ} [Fact l.Prime] (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) :
    Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥K.1 := by
  have := K.2
  rw [← AlgHom.card ℚ_[l] ↥K.1 (Loc.Om l), ← Nat.card_eq_fintype_card]
  refine Nat.card_eq_of_bijective (fun τ => LL.1.val.comp τ) ⟨?_, ?_⟩
  · intro a b hab
    ext x
    exact DFunLike.congr_fun hab x
  · intro τ
    exact ⟨τ.codRestrict LL.1.toSubalgebra (h τ), by ext x; rfl⟩

-- The concrete local period data makes `Module` synthesis for `DdR` exceed the default budget.
set_option synthInstance.maxHeartbeats 100000 in
open Formalism.BasicNotions Formalism.WeaklyAdmissibleFiltrations in
theorem finrank_DdR_local {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : Loc.FinExt l)
    (h : ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Loc.Om l) (x : ↥K.1), τ x ∈ LL.1) {m : ℕ} (hm : 0 < m)
    (ρ : Representation ↥LL.1 ↥(Loc.GK K) (Fin m → ↥LL.1))
    (hρ : finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = finrank ℚ_[l] ↥K.1 * m) (a : ℤ) :
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) ∧
    finrank ↥LL.1 ↥(DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Fin m → ↥LL.1) a) =
      ∑ᶠ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ a) := by
  have hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hpos : 0 < finrank ↥LL.1 ↥(DdR (P.PD K) ρ) := by
    rw [hρ]
    exact Nat.mul_pos Module.finrank_pos hm
  have hD : FiniteDimensional ↥LL.1 ↥(DdR (P.PD K) ρ) := FiniteDimensional.of_finrank_pos hpos
  have hc := card_emb _ _ h
  exact finrank_DdR_finsum (P.PD K) ρ hc a

end GlobalTheory.DeRhamSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsCrisPOfIsCrisDR
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.FundSeq

def OntoAt (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ ι : Per.Bcris l →+* Per.BdR l, Per.IsCrisDR l ι →
    (∀ u : Per.Bcris l, ∃ x : Per.Bcris l, ι x ∈ Per.FilD l 0 ∧ x - Per.φB l x = u) ∧
    (∀ w : Per.BdR l, ∃ b : Per.Bcris l, Per.φB l b = b ∧ ι b - w ∈ Per.FilD l 0)

theorem pair_onto {B D : Type} [AddCommGroup B] [AddCommGroup D] (φ : B →+ B) (ι : B →+ D) (F : Set D)
    (h1 : ∀ u, ∃ x, x - φ x = u) (h2 : ∀ w, ∃ b, φ b = b ∧ ι b - w ∈ F) (u : B) (w : D) :
    ∃ x y, y ∈ F ∧ x - φ x = u ∧ ι x - y = w := by
  obtain ⟨x0, hx0⟩ := h1 u
  obtain ⟨b, hb, hF⟩ := h2 (w - ι x0)
  refine ⟨x0 + b, _, hF, ?_, ?_⟩
  · rw [map_add (f := _), hb, ← hx0]; abel
  · rw [map_add (f := _)]; abel

variable {l : ℕ} [Fact l.Prime]

theorem exists_restrict_aCris_bdRPlus {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) :
    ∃ j : Per.Acris l →+* Per.BdRp l, IsCrisP j ∧ ∀ x : Per.Acris l,
      ι (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (j x) := by
  obtain ⟨j, h1, h2, h3⟩ := GlobalTheory.CrisIncl.exists_restrict l ι h
  exact ⟨j, ⟨h2, h3⟩, h1⟩

theorem eq_core_of_isCrisDR {ι : Per.Bcris l →+* Per.BdR l} (h : Per.IsCrisDR l ι) (C : Core l) :
    ι = C.ι := by
  obtain ⟨j, hj, hι⟩ := exists_restrict_aCris_bdRPlus h
  have e : j = C.j := (crisP_unique_equivariant l C.j C.j_cris).1 j hj
  refine GlobalTheory.RingIface.bcris_ext l fun x => ?_
  rw [hι, C.ι_j, e]

theorem ontoAt_of_core (C : Core l) (h1 : C.OneSubPhiOnto) (h2 : C.FundOnto) : OntoAt l := by
  intro ι hι
  rw [eq_core_of_isCrisDR hι C]
  refine ⟨fun u => ?_, h2⟩
  obtain ⟨x, y, hy, hx, hxy⟩ := pair_onto (Per.φB l).toAddMonoidHom C.ι.toAddMonoidHom
    (Per.FilD l 0 : Set (Per.BdR l)) h1 h2 u 0
  exact ⟨x, (sub_eq_zero.1 hxy : C.ι x = y) ▸ hy, hx⟩

theorem pair_onto_of_tied {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) (h : OntoAt l)
    (K : FinExt l) (u : P.R.B) (w : P.R.BdR) :
    ∃ (x : P.R.B) (y : P.R.BdR), y ∈ (P.PD K).Fil 0 ∧ x - (P.PD K).φ x = u ∧ (P.PD K).ι x - y = w := by
  obtain ⟨h1, h2⟩ := h _ T.incl
  have H := pair_onto (P.φB : P.R.B →+* P.R.B).toAddMonoidHom
    (P.ιB : P.R.B →+* P.R.BdR).toAddMonoidHom ((P.PD K).Fil 0 : Set P.R.BdR) (fun u => ?_) (fun w => ?_) u w
  · obtain ⟨x, y, hy, hx, hxy⟩ := H
    exact ⟨x, y, hy, by rw [P.PD_φ]; exact hx, by rw [P.PD_ι]; exact hxy⟩
  · obtain ⟨x, -, hx⟩ := h1 (T.eB u)
    obtain ⟨x, rfl⟩ := T.eB.surjective x
    refine ⟨x, T.eB.injective ?_⟩
    rw [← hx, map_sub, ← T.frob]
    rfl
  · obtain ⟨b, hb, hF⟩ := h2 (T.eD w)
    obtain ⟨b, rfl⟩ := T.eB.surjective b
    refine ⟨b, T.eB.injective ((T.frob b).trans hb), (T.fil K 0 _).2 ?_⟩
    have e : T.eB.symm.toRingHom (T.eB b) = b := T.eB.symm_apply_apply b
    rw [RingHom.comp_apply, e] at hF
    rw [map_sub]
    exact hF

theorem surjective_half_of_onto (h : ∀ (l : ℕ) [Fact l.Prime], OntoAt l) (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.LocalSituation.adm1 D :=
  fun l _ K u w => pair_onto_of_tied (D.locT l) (h l) K u w

end GlobalTheory.FundSeq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.AntiRam

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem valuation_comap_lt_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (y : Ω) :
    (A.comap c.symm.toRingHom).valuation y < 1 ↔ A.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, ← map_inv₀, map_eq_zero_iff _ c.symm.injective]
  rfl

theorem exists_conj_mem_Ine (c : Ω ≃+* Ω) (κ : E → E)
    (hc : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (κ x)) (hκ : ∀ x, κ (κ x) = x)
    (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ σ' : G E Ω, (∀ x, σ' x = c (σ (c.symm x))) ∧ σ' ∈ Ine (F := E) (A.comap c.symm.toRingHom) := by
  have hs : ∀ x, c.symm (algebraMap E Ω x) = algebraMap E Ω (κ x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofRingEquiv (f := (c.symm.trans (σ : Ω ≃ₐ[E] Ω).toRingEquiv).trans c)
    (fun x => by
      show c (σ (c.symm (algebraMap E Ω x))) = _
      rw [hs, AlgEquiv.commutes, hc, hκ])
  have h' : ∀ x, σ' x = c (σ (c.symm x)) := fun _ => rfl
  have hm : ∀ y, y ∈ A.comap c.symm.toRingHom ↔ c.symm y ∈ A := fun _ => Iff.rfl
  refine ⟨σ', h', ?_, fun x hx => ?_⟩
  · change σ' ∈ Dec (F := E) _
    rw [mem_Dec]
    ext y
    obtain ⟨z, rfl⟩ := σ'.surjective y
    rw [← AlgEquiv.smul_def σ' z, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def,
      hm, hm, h', RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ.1]
  · rw [valuation_comap_lt_one, map_sub, h', RingEquiv.symm_apply_apply]
    refine hσ.2 _ ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hm x).1 hx

end General

theorem ramExactly_conj : ∀ (D : D7) (M : Type) [CommGroup M] (ψ : G D.host.E D.nd.Om →* M) (Q : Set (PlE D.host)), AntiHom D.ntw.cc ψ → RamExactly ψ Q → ∀ P ∈ Q, ∀ P' : PlE D.host, IsConjPl D.host P P' → P' ∈ Q := by
  intro D M _ ψ Q hA hR P hP P' hPP
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

end GlobalTheory.AntiRam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal

namespace GlobalTheory.ToricDenom

def IsClassTerm {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (y : (Af E)ˣ) (T : ℂ) : Prop :=
  ∃ S : ℂ → ℂ, IsLatSum φ (2 * s) κ (lattice c y) S ∧ T = ((finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ))⁻¹ * S 0

theorem isToricSum_iff {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (c : Ideal (OF E)) (χ : HChar E) (T : ℂ) :
    IsToricSum φ s κ c χ T ↔ Finite (PicO c) ∧ ∃ t : PicO c → ℂ, (∀ q, IsClassTerm φ s κ c χ q.out (t q)) ∧ T = ∑ᶠ q, t q := by
  refine and_congr_right fun _ => ⟨fun ⟨S, hS, hT⟩ => ⟨_, fun q => ⟨S q, hS q, rfl⟩, hT⟩, fun ⟨t, ht, hT⟩ => ?_⟩
  choose S hS hS' using ht
  exact ⟨S, hS, by rw [hT]; exact finsum_congr hS'⟩

def IsHostDatum {R : Ranks} (H : Host R) {I : Type} [Fintype I] (φ : I → H.E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF H.E))
    (χ : HChar H.E) : Prop :=
  IsCMType φ ∧ (∀ τ τ', φ τ H.sqrtMinusD = φ τ' H.sqrtMinusD) ∧ 1 ≤ s ∧ (∀ τ, 1 ≤ κ τ) ∧ IsBaseCond 𝔣 ∧ IsValChar φ s κ 𝔣 ∅ χ

def below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (OF E) :=
  P.under (OF E)

theorem over_below {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Over P (below P) := rfl


open Classical in
def belowSet {E : Type} [Field E] [NumberField E] (Q : Finset (HeightOneSpectrum (𝓞 E))) : Finset (HeightOneSpectrum (OF E)) :=
  Q.image below

theorem splits_below {R : Ranks} (H : Host R) {P : HeightOneSpectrum (𝓞 H.E)} (h : IsSplitPl H P) : Splits (below P) := by
  obtain ⟨x, hx, hx'⟩ := h
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv H.conj.toRingEquiv
  have hc : ∀ a : 𝓞 H.E, ((c a : 𝓞 H.E) : H.E) = H.conj (a : H.E) := fun a => rfl
  refine ⟨P, P.comap c.toRingHom c.surjective, fun e => ?_, rfl, ?_⟩
  · have : x ∈ (P.comap c.toRingHom c.surjective).asIdeal := e ▸ hx
    exact hx' (c x) (hc x) this
  · ext a
    have : c (algebraMap (OF H.E) (𝓞 H.E) a) = algebraMap (OF H.E) (𝓞 H.E) a := by
      apply RingOfIntegers.ext
      apply H.φ₀.injective
      show H.φ₀ (H.conj ((a : maximalRealSubfield H.E) : H.E)) = H.φ₀ ((a : maximalRealSubfield H.E) : H.E)
      rw [H.toHostAx.conjE_apply]
      exact (a : maximalRealSubfield H.E).2 H.φ₀
    show c (algebraMap (OF H.E) (𝓞 H.E) a) ∈ P.asIdeal ↔ algebraMap (OF H.E) (𝓞 H.E) a ∈ P.asIdeal
    rw [this]

section Record

variable {D : D7} {N : NData D.R D.host D.what₂} (X : NTw D.R D.host D.what₂ D.LL0 N)

abbrev Kbar (i : X.Tw) : Type := AlgebraicClosure (FractionRing (X.O i))

def toBar (i : X.Tw) : FractionRing (X.O0 i) →+* Kbar X i :=
  (algebraMap (FractionRing (X.O i)) (Kbar X i)).comp
    (IsFractionRing.lift (g := (algebraMap (X.O i) (FractionRing (X.O i))).comp (algebraMap (X.O0 i) (X.O i)))
      ((IsFractionRing.injective (X.O i) (FractionRing (X.O i))).comp (X.O_inj i)))

def IsRecMap (i : X.Tw) (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) {c : Ideal (OF D.host.E)} (π : PicO c →* X.RCG i Q) : Prop :=
  ∀ P, P ∉ X.S0 i → P ∉ Q → ∀ σ : G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ →
    π (QuotientGroup.mk (unifAt P)) = (X.art i Q σ)⁻¹

def IsToricEltAt (i : X.Tw) (ι : ℂ →+* Kbar X i) (lam : X.abelian₂ i) (s : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (φ : I → D.host.E →+* ℂ) (κ : I → ℕ) (𝔣 : Ideal (OF D.host.E)) (χ : HChar D.host.E)
    (u : Kbar X i),
    IsHostDatum D.host φ s κ 𝔣 χ ∧
    (∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) ∧
    (∀ P, P ∉ X.S0 i → algebraMap (X.O i) (Kbar X i) (X.Xv i lam P) * ι (val χ P : ℂ) = 1) ∧
    u ≠ 0 ∧
    ∀ Q, BlochKatoReduction.Gen.QOk X i Q → Finite (PicO (condQ 𝔣 (belowSet Q))) ∧
      ∃ (π : PicO (condQ 𝔣 (belowSet Q)) →* X.RCG i Q) (T : PicO (condQ 𝔣 (belowSet Q)) → ℂ),
        IsRecMap X i Q π ∧ (∀ q, IsClassTerm φ s κ (condQ 𝔣 (belowSet Q)) χ q.out (T q)) ∧
        ∀ δ, algebraMap (FractionRing (X.O i)) (Kbar X i) (X.th i Q lam δ) = u * ι (∑ᶠ q ∈ {q | π q⁻¹ = δ}, T q)

def atSide {i : X.Tw} (b : Bool) (ι : ℂ →+* Kbar X i) : ℂ →+* Kbar X i := if b then ι else ι.comp (starRingEnd ℂ)

def IsToricElt : Prop :=
  ∀ i, X.NonzeroIndexPlace i → ∃ ι : ℂ →+* Kbar X i, (∀ x : D.LL0, ι (D.what₂.embLL (x : D.what₂.LL)) = toBar X i (X.emb0 i x)) ∧
    ∀ (lam : X.abelian₂ i) (s : ℕ), BlochKatoReduction.Gen.SOk X i lam s → IsToricEltAt X i (atSide X (X.sideL i lam) ι) lam s

variable {X}

theorem placesBelow_splitCoprimeConductor_of_admissible {i : X.Tw} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (hQ : BlochKatoReduction.Gen.QOk X i Q) {𝔣 : Ideal (OF D.host.E)}
    (h𝔣 : ∀ P, (below P).asIdeal ∣ 𝔣 → P ∈ X.S0 i) :
    IsFinSetSplitPlacesCoprimeConductor 𝔣 (belowSet Q) ∧ ∀ q ∈ belowSet Q, ((X.l i : ℕ) : OF D.host.E) ∉ q.asIdeal := by
  classical
  constructor
  · intro q hq
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨splits_below D.host (hQ.1 P hP), fun h => Finset.disjoint_left.1 hQ.2.1 hP (h𝔣 P h)⟩
  · intro q hq h
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
    refine Finset.disjoint_left.1 hQ.2.1 hP (X.twistExcludedPlaces_contains_residueChar i ?_)
    have : algebraMap (OF D.host.E) (𝓞 D.host.E) ((X.l i : ℕ) : OF D.host.E) ∈ P.asIdeal := h
    rwa [map_natCast] at this

end Record

end GlobalTheory.ToricDenom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsoluteIrreducibilitySpan
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.Proof.AbsoluteIrreducibilitySpan


open Formalism.MainNotions.N in
theorem absIrr_of_span {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (ha : 0 < a) (ρ : Γ →* GL (Fin a) k)
    (M : Γ → Matrix (Fin a) (Fin a) k) (c : Γ → k)
    (hM : ∀ g, M g = c g • (ρ g : Matrix (Fin a) (Fin a) k))
    (h : Submodule.span k (Set.range M) = ⊤) : AbsIrrSub ρ ⊤ := by
  classical
  set K := AlgebraicClosure k
  have htop : Submodule.span K ((fun v : Fin a → k => (algebraMap k K) ∘ v) ''
      ((⊤ : Submodule k (Fin a → k)) : Set (Fin a → k))) = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq]
    apply Submodule.span_mono
    rintro _ ⟨j, rfl⟩
    refine ⟨Pi.single j 1, trivial, ?_⟩
    ext x
    by_cases hx : x = j
    · subst hx; simp
    · simp [hx]
  unfold AbsIrrSub
  rw [htop]
  have : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W' _ hW => ?_⟩
  have key : ∀ X : Matrix (Fin a) (Fin a) k, ∀ v ∈ W', (X.map (algebraMap k K)).mulVec v ∈ W' := by
    intro X
    have hX : X ∈ Submodule.span k (Set.range M) := h ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v hv
      have h1 : (M g).map (algebraMap k K) = algebraMap k K (c g) •
          ((mapRep (algebraMap k K) ρ g : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) := by
        ext p q
        simp [hM, mapRep]
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hW g v hv)
    | zero => intro v hv; simp
    | add x y _ _ hx hy =>
      intro v hv
      rw [Matrix.map_add _ (map_add _), Matrix.add_mulVec]
      exact W'.add_mem (hx v hv) (hy v hv)
    | smul r x _ hx =>
      intro v hv
      have h1 : (r • x).map (algebraMap k K) = algebraMap k K r • x.map (algebraMap k K) := by
        ext p q
        simp
      rw [h1, Matrix.smul_mulVec]
      exact W'.smul_mem _ (hx v hv)
  by_cases hb : W' = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
  obtain ⟨b, hb'⟩ := Function.ne_iff.mp hv0
  rw [eq_top_iff, ← (Pi.basisFun K (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  have h2 := W'.smul_mem (v b)⁻¹ (key (Matrix.single j b 1) v hv)
  have hb2 : v b ≠ 0 := hb'
  have h3 : (v b)⁻¹ • ((Matrix.single j b (1 : k)).map (algebraMap k K)).mulVec v = Pi.basisFun K (Fin a) j := by
    rw [Matrix.map_single, map_one, Matrix.single_mulVec]
    ext x
    by_cases hx : x = j
    · subst hx; simp [hb2]
    · simp [hx]
  rw [h3] at h2
  exact h2

end GlobalTheory.Proof.AbsoluteIrreducibilitySpan
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RestrictionH1MemBlochKato
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.BKIntegralToRational

theorem exists_mul_pow_eq {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A}
    (hu : ¬ IsUnit p) (a : FractionRing A) :
    ∃ (x : A) (N : ℕ), a * algebraMap A (FractionRing A) p ^ N = algebraMap A (FractionRing A) x := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := A) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd0 hϖ
  have h1 : ϖ ∣ p := by
    rw [← Ideal.mem_span_singleton, ← hϖ.maximalIdeal_eq]
    exact hu
  obtain ⟨c, hc⟩ : d ∣ p ^ N := hN.dvd.trans (pow_dvd_pow_of_dvd h1 N)
  refine ⟨n * c, N, ?_⟩
  have hd1 : algebraMap A (FractionRing A) d ≠ 0 := by
    simpa using hd0
  rw [← map_pow, hc, map_mul, map_mul]
  field_simp

theorem continuous_div_mk {O₀ O' : Type} [CommRing O₀] [IsDomain O₀] [IsDiscreteValuationRing O₀]
    [TopologicalSpace O₀] [IsTopologicalRing O₀] (had : IsAdic (IsLocalRing.maximalIdeal O₀))
    [CommRing O'] [IsDomain O'] (ι : O₀ →+* O') {d : O₀} (hd : d ≠ 0) (hd' : ι d ≠ 0) :
    Continuous fun x : O₀ => (Submodule.Quotient.mk (algebraMap O' (FractionRing O') (ι x) /
      algebraMap O' (FractionRing O') (ι d)) : KmodO O') := by
  have hd1 : algebraMap O' (FractionRing O') (ι d) ≠ 0 := by simpa using hd'
  have hop : IsOpen ((Ideal.span {d} : Ideal O₀) : Set O₀) := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O₀
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
    have := (isAdic_iff.1 had).1 N
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at this
    rwa [Ideal.span_singleton_eq_span_singleton.2 hN]
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => y - x) ⁻¹' ((Ideal.span {d} : Ideal O₀) : Set O₀),
    hop.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  obtain ⟨c, hc⟩ : d ∣ y - x := Ideal.mem_span_singleton.1 hy
  rw [Submodule.Quotient.eq]
  refine ⟨ι c, ?_⟩
  rw [← sub_div, ← map_sub, ← map_sub, hc, map_mul, map_mul]
  simp only [Algebra.linearMap_apply]
  field_simp

section Bridge

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem continuous_of_toLL {X : Type} [TopologicalSpace X] (f : X → O₀)
    (h : Continuous fun x => Bw.toLL (f x)) : Continuous f := by
  have h1 : Continuous fun x => Bw.eO (f x) := continuous_induced_rng.2 h
  simpa [Function.comp_def] using Bw.eO_symm_cont.comp h1

theorem continuous_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (j : Fin m) : Continuous fun g => f g j := by
  apply continuous_of_toLL Bw
  have := ((continuous_apply j).comp hf.1.1).comp Bw.e_cont
  simpa [Function.comp_def] using this

theorem cocycle_of_crys {T : (Ω ≃ₐ[E] Ω) →* GL (Fin m) O₀} {f : ↥Gw → Fin m → O₀}
    (hf : IsCrysCocycle Bw P T f) (g h : ↥Gw) (j : Fin m) :
    f (g * h) j = f g j + ∑ b, ((T g : GL (Fin m) O₀) : Matrix (Fin m) (Fin m) O₀) j b * f h b := by
  apply toLL_injective Bw
  have := congrFun (hf.1.2 (Bw.e g) (Bw.e h)) j
  simpa [← map_mul, LocBridge.rep, Matrix.mulVec, dotProduct, Matrix.toLinAlgEquiv'_apply] using this

end Bridge

section Main

variable (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i) (k : ℕ)

variable (ψ : GE D →* (D.ntw.Ok i k)ˣ) (v : PlE D.host) (hv : v ∈ placesOver D.host.E (D.ntw.l i))
  (hψ : ∀ σ ∈ decAt D v, ψ σ = 1)


end Main

end GlobalTheory.BKIntegralToRational
end
end
