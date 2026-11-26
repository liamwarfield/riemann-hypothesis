module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSBOfIsNatDatum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralEqVolumeSumCharacterTwistedCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTanAtGTv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaIntegralStandardPairFirstEqSecond
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleConstantsEqOfSameLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFrameLocalCompactMembership
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFrameLocalCompactMembership
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.ChKO

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hatL_map {a b : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {Λ' : Submodule (𝓞 E) (Fin b → E)}
    (f : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin b → E ⊗[F] Formalism.L2.Herm.Af F))
    (hf : ∀ x ∈ Λ, ∃ y ∈ Λ', (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (y i)) =
      f fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ, f x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, e⟩ := hf x hx
    exact Submodule.subset_span ⟨y, hy, e⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ r hx


open GlobalTheory.Doubling in
theorem pairVec_mem_hatL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} (x : Fin a → E ⊗[F] Formalism.L2.Herm.Af F) (y : Fin b → E ⊗[F] Formalism.L2.Herm.Af F) :
    pairVec e x y ∈ Formalism.L2.Herm.hatL (F := F) (sumLat e Λ Λ') ↔
      x ∈ Formalism.L2.Herm.hatL (F := F) Λ ∧ y ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ) (LinearMap.funLeft _ _ (e ∘ .inl)) (fun x hx => ⟨_, hx.1, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · have := hatL_map (Λ := sumLat e Λ Λ') (Λ' := Λ') (LinearMap.funLeft _ _ (e ∘ .inr)) (fun x hx => ⟨_, hx.2, rfl⟩) _ h
    convert this using 1
    funext i; simp [LinearMap.funLeft_apply]
  · let f₁ : (Fin a → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e u 0
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    let f₂ : (Fin b → E ⊗[F] Formalism.L2.Herm.Af F) →ₗ[Formalism.L2.Herm.intAf F E] (Fin c → E ⊗[F] Formalism.L2.Herm.Af F) :=
      { toFun := fun u => pairVec e 0 u
        map_add' := fun u v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
        map_smul' := fun r v => funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp }
    have h1 := hatL_map (Λ' := sumLat e Λ Λ') f₁ (fun u hu => ⟨pairVec e u 0, (pairVec_mem_sumLat e).2 ⟨hu, zero_mem _⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁]⟩) _ h.1
    have h2 := hatL_map (Λ' := sumLat e Λ Λ') f₂ (fun u hu => ⟨pairVec e 0 u, (pairVec_mem_sumLat e).2 ⟨zero_mem _, hu⟩,
      funext fun j => by obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₂]⟩) _ h.2
    convert add_mem h1 h2 using 1
    funext j
    obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [f₁, f₂]


open GlobalTheory.Doubling in
theorem isFrame_blkGL {a b c : ℕ} (e : Fin a ⊕ Fin b ≃ Fin c) {Λ : Submodule (𝓞 E) (Fin a → E)}
    {Λ' : Submodule (𝓞 E) (Fin b → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)} {β' : GL (Fin b) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ') : IsFrame (blkGL e (β, β')) (sumLat e Λ Λ') := by
  intro x
  rw [← pairVec_eta e x, pairVec_mem_hatL, h, h']
  change _ ↔ ∀ i, (blkMat e (β⁻¹).val (β'⁻¹).val *ᵥ _) i ∈ _
  rw [blkMat_mulVec]
  refine ⟨fun H j => ?_, fun H => ⟨fun i => ?_, fun i => ?_⟩⟩
  · obtain ⟨i | i, rfl⟩ := e.surjective j
    · rw [pairVec_inl]; exact H.1 i
    · rw [pairVec_inr]; exact H.2 i
  · have := H (e (.inl i)); rwa [pairVec_inl] at this
  · have := H (e (.inr i)); rwa [pairVec_inr] at this

theorem isFrame_neg {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) : IsFrame (-β) Λ := by
  intro x
  rw [h, inv_neg, Units.val_neg, neg_mulVec]
  exact forall_congr' fun i => neg_mem_iff.symm

theorem int_change {a : ℕ} {Λ : Submodule (𝓞 E) (Fin a → E)} {β β' : GL (Fin a) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (i j : Fin a) : (β'⁻¹ * β).val i j ∈ Formalism.L2.Herm.intAf F E := by
  have h1 := (h (β.val *ᵥ Pi.single j 1)).2 fun l => by
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 := (h' _).1 h1 i
  rwa [mulVec_mulVec, mulVec_single_one] at h2

end Lat

variable {D : D7}

theorem isEquiv_val (w : Pl D.host.E) :
    (ValuativeRel.valuation (Kw w)).IsEquiv (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Kw w) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem change_mem_KO {a : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}
    (h : IsFrame β Λ) (h' : IsFrame β' Λ) (w : Pl D.host.E) : (loc w β')⁻¹ * loc w β ∈ KO (Kw w) (Fin a) := by
  have key : ∀ {β β' : GL (Fin a) (Formalism.IndefR.Lev.EAf D)}, IsFrame β Λ → IsFrame β' Λ → ∀ i j,
      ((loc w β')⁻¹ * loc w β).val i j ∈ (ValuativeRel.valuation (Kw w)).integer := fun {β β'} h h' i j => by
    have h2 := (mem_OA_iff _).1 (int_change h h' i j) w
    rw [← map_inv, ← map_mul]
    exact (isEquiv_val w).le_one_iff_le_one.2 h2
  refine (mem_KO_iff _).2 ⟨key h h', ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact key h' h

theorem reGL_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) {g : GL a k} (hg : g ∈ KO k a) :
    GlobalTheory.StepData.reGL e g ∈ KO k b := by
  obtain ⟨h1, h2⟩ := (mem_KO_iff _).1 hg
  refine (mem_KO_iff _).2 ⟨fun i j => h1 _ _, fun i j => ?_⟩
  rw [← map_inv]
  exact h2 _ _

theorem scalar_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a : Type} [Fintype a] [DecidableEq a] (u : kˣ) (hu : ValuativeRel.valuation k u = 1) :
    Units.map (Matrix.scalar a).toMonoidHom u ∈ KO k a := by
  have key : ∀ u : kˣ, ValuativeRel.valuation k u = 1 → ∀ i j,
      (Units.map (Matrix.scalar a).toMonoidHom u).val i j ∈ (ValuativeRel.valuation k).integer := fun u hu i j => by
    change Matrix.diagonal (fun _ => (u : k)) i j ∈ _
    rw [diagonal_apply]
    split_ifs
    exacts [hu.le, zero_mem _]
  refine (mem_KO_iff _).2 ⟨key u hu, ?_⟩
  rw [← map_inv]
  exact key _ (by rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one])

theorem val_xiAt (w : Pl D.host.E)
    (hw : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) :
    ValuativeRel.valuation (Kw w) (xiAt w) = 1 := by
  have hn : ∀ n : ℕ, n ∣ D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK → w.valuation D.host.E (n : D.host.E) = 1 := by
    rintro n ⟨m, hm⟩
    have : (n : 𝓞 D.host.E) ∉ w.asIdeal := fun h => hw (by rw [hm, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
    have := (w.valuation_eq_one_iff_notMem (K := D.host.E)).2 this
    rwa [map_natCast] at this
  have h1 := hn _ (dvd_mul_left _ _)
  have h2 := hn D.host.d (Dvd.dvd.mul_right (dvd_mul_left _ _) _)
  have h3 : w.valuation D.host.E D.host.sqrtMinusD = 1 := by
    have := congrArg (w.valuation D.host.E) D.host.sqrtMinusD_sq
    rw [map_pow, Valuation.map_neg, h2] at this
    exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 this
  have h4 : w.valuation D.host.E D.host.xi0 = 1 := by
    unfold Formalism.BasicNotions.Host.xi0
    rw [map_div₀, map_mul, h1, h3, Valuation.map_neg, map_one, mul_one, div_one]
  refine (isEquiv_val w).eq_one_iff_eq_one.2 ?_
  exact (w.valuedAdicCompletion_eq_valuation' _).trans h4

theorem changes_mem_KO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j), SquareStanding G t →
      IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1))) → IsFrame X.rA'.β (G.Λ (.grid i j)) → IsFrame X.rW.β (latX G i j) →
      ∀ w ∈ locPl G t, chA B t X w ∈ KO (Kw w) _ ∧ chB B t X w ∈ KO (Kw w) _ ∧ chX B t X w ∈ KO (Kw w) _ := by
  intro D T L sc G μ₀ hL B t i j X hS hA hA' hW w hw
  refine ⟨reGL_mem_KO _ (invT_mem_KO (change_mem_KO (B.isFrame_β hL i.2 j.2) hA w)),
    reGL_mem_KO _ (mul_mem (scalar_mem_KO _ (val_xiAt w (hS.2 w hw))) (change_mem_KO (B.isFrame_β hL i.2.le j.2.le) hA' w)),
    reGL_mem_KO _ (change_mem_KO hW (isFrame_blkGL finSumFinEquiv (B.isFrame_β hL i.2.le j.2)
      (isFrame_neg (B.isFrame_β hL i.2 j.2.le))) w)⟩

end GlobalTheory.TopFlip.ChKO

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridFrameLocalCompactMembershipStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_frame_local_compact_membership : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j), SquareStanding G t →
      IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1))) → IsFrame X.rA'.β (G.Λ (.grid i j)) → IsFrame X.rW.β (latX G i j) →
      ∀ w ∈ locPl G t, chA B t X w ∈ KO (Kw w) _ ∧ chB B t X w ∈ KO (Kw w) _ ∧ chX B t X w ∈ KO (Kw w) _ := by
  first | exact @GlobalTheory.TopFlip.ChKO.changes_mem_KO | exact GlobalTheory.TopFlip.ChKO.changes_mem_KO | (intros; apply GlobalTheory.TopFlip.ChKO.changes_mem_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.TopFlip.ChartB

theorem reindex_blocks {K C : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (ρ : Fin p ⊕ Fin q ≃ C)
    (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P R : Matrix (Fin p) (Fin p) K)
    (Q S : Matrix (Fin q) (Fin q) K) (r : Fin n) (c : C) :
    (x * (Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S)) r ((finSumFinEquiv.symm.trans ρ).symm c) =
    (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))) r ((e.symm.trans ρ).symm c) := by
  have h : Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
      (Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix id (e.symm.trans finSumFinEquiv).symm := by
    have h1 : GlobalTheory.Doubling.blkMat finSumFinEquiv P Q * GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix (e.symm.trans finSumFinEquiv).symm
          (e.symm.trans finSumFinEquiv).symm := by
      unfold GlobalTheory.Doubling.blkMat GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
      rw [submatrix_mul_equiv, fromBlocks_multiply]
      ext a b
      simp
    rw [Matrix.mul_assoc, h1, submatrix_mul_equiv]
  rw [Matrix.mul_assoc, h, Matrix.mul_assoc]
  simp [Matrix.mul_apply]

variable {D : D7}

theorem adj_coord (S X : HSp D) (y : Matrix (Fin S.rank) (Fin X.rank) (AE D)) :
    (S.gram⁻¹).map (incA D) * ((HMul.hMul yᵀ (incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      y.map (cA D) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = S.gram.map (incA D) := by
    ext a b
    exact congrArg (incA D) (show star (S.gram b a) = S.gram a b from S.herm.eq (S.frame b) (S.frame a))
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram, Matrix.one_mul]
  rfl

theorem linB_ptB {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linB B t i j w (ptB e u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β (i + 1) j)).val))) := by
  have h1 := adj_coord (spW₁ G i j) (spX G i j) (u.submatrix id (e.symm.trans finSumFinEquiv).symm)
  have h2 : (((spX G i j).gram.map (incA D)).map (toEAf D)).map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) := by
    rw [GlobalTheory.Doubling.gram_hsum]
    refine Matrix.ext fun a b => ?_
    refine (GlobalTheory.FunObj.Good.cpt_incA w _).trans ?_
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h3 : (frX B i j).val.map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val
      (-(loc w (B.β (i + 1) j)).val) := by
    refine Matrix.ext fun a b => ?_
    change cpt w (GlobalTheory.Doubling.blkMat finSumFinEquiv (B.β i (j + 1)).val (-(B.β (i + 1) j).val) a b) = _
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h4 : (frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) (ptB e u)).map (cpt w) =
      ((loc w (B.β i j))⁻¹).val * ((u.map (fun a => cpt w (toEAf D (cA D a)))).submatrix id
        (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)))) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [← h2, ← h3]
    unfold frMapAdj
    erw [h1]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine Matrix.ext fun r c => ?_
  unfold linB
  rw [h4]
  exact reindex_blocks e _ _ _ _ _ _ _ _ c


open GlobalTheory.FlipMatch.ChartOpp hiding isHalf_of_mulG in
theorem exists_mixChart_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  intro D T L sc G μ₀ _ W B t i j M _ e Bs Γ X _ _ h _ _ v w hw jj hjj _ cc hcc
  classical

  have hε : atPl w 1 = GlobalTheory.EmbChart.idem (Bs.τ v) :=
    (GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hw ▸ GlobalTheory.EmbChart.isIdemAt_idem (Bs.τ v))).symm
  have hsum : GlobalTheory.EmbChart.idem (Bs.τ v) + cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) := by
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl
  have hii := GlobalTheory.SrcHalfOne.idem_mul_self (Bs.τ v)
  have hic : GlobalTheory.EmbChart.idem (Bs.τ v) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) = 0 :=
    (GlobalTheory.EmbChart.isSplitIdem_idem (Bs.τ v)).2.1
  have hcc' : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by rw [← map_mul, hii]
  have hb₁ : GlobalTheory.EmbChart.idem (Bs.τ v) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      GlobalTheory.EmbChart.idem (Bs.τ v) := by rw [← hsum, mul_add, hii, hic, add_zero]
  have hb₂ : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by
    rw [← hsum, mul_add, mul_comm (cA D _) (GlobalTheory.EmbChart.idem _), hic, zero_add, hcc']
  rw [hε]

  have hzero : cpt w (toEAf D (cA D (GlobalTheory.EmbChart.idem (Bs.τ v)))) = 0 := by
    rw [← hjj]
    exact (congrArg jj (GlobalTheory.SrcHalfOne.piW_cA_idem (Bs.τ v))).trans (map_zero jj)
  have hE : ∀ x : D.host.E, jj (Bs.τ v x) = algebraMap D.host.E (Kw w) x := fun x => by
    rw [← GlobalTheory.FunObj.Good.cpt_incA w x, ← hjj]
    exact congrArg jj (GlobalTheory.LocFrame.piW_incA (Bs.τ v) x).symm
  have hcA : ∀ a, jj (piW ((Bs.τ v).comp D.sp.cm.sig) a) = cpt w (toEAf D (cA D a)) := fun a => by
    rw [← hjj]
    exact congrArg jj (GlobalTheory.SrcHalfOne.piW_cA (Bs.τ v) a).symm

  obtain ⟨κ, hκ⟩ : ∃ κ : D.host.E →+* Kw w, κ = algebraMap D.host.E (Kw w) := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : GL (Fin (spW₁ G i j).rank) (Kw w),
    Bp = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.V'.bas v) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w),
    C = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.W.bas v) := ⟨_, rfl⟩
  have hG₁ : ((spW₁ G i j).gram.map κ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero κ).2 (GlobalTheory.RouteCoords.gram_det_ne _)
  have hξ : xiAt w ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hCc : C.val * cc.val = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [hC]; exact hcc
  obtain ⟨g, hg⟩ := chart_algebra e Bp C cc _ hG₁ (loc w (B.β i j)) (loc w (B.β i (j + 1))) (loc w (B.β (i + 1) j))
    ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) (xiAt w) hξ hCc
  refine ⟨g, ?_⟩

  have hκm : ∀ {a b : Type} (Z : Matrix a b D.host.E), (Z.map (Bs.τ v)).map jj = Z.map κ := fun Z =>
    Matrix.ext fun _ _ => by rw [hκ]; exact hE _
  have hX : ∀ u, (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      (Bp⁻¹).val * u.map (fun a => cpt w (toEAf D a)) * ((C⁻¹).val)ᵀ := fun u => by
    unfold coX
    rw [map_mul_equiv, map_mul_equiv, Matrix.transpose_map, Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW (Bs.τ v))) = u.map (fun a => cpt w (toEAf D a)) := Matrix.ext fun _ _ => hjj _
    rw [this, hBp, hC]
    rfl
  have hJ1 : (Γ.V'.J.map (Bs.τ v)).map jj = -((spW₁ G i j).gram.map κ) := by
    rw [hκm, h.JW₁]
    ext a b
    simp
  have hJ2 : ((Γ.W.J.map (Bs.τ v))ᵀ).map jj = xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) := by
    rw [Matrix.transpose_map, hκm, h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm a with a | a <;> rcases e.symm b with b | b <;> simp [xiAt, hκ]
  have hY : ∀ u, (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      -(Bp.valᵀ * (-((spW₁ G i j).gram.map κ)) * u.map (fun a => cpt w (toEAf D (cA D a))) *
        (xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ)) * C.val) := fun u => by
    unfold coY
    rw [Matrix.map_neg _ (map_neg jj), map_mul_equiv, map_mul_equiv, map_mul_equiv, map_mul_equiv, hJ1, hJ2,
      Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW ((Bs.τ v).comp D.sp.cm.sig))) = u.map (fun a => cpt w (toEAf D (cA D a))) :=
      Matrix.ext fun _ _ => hcA _
    rw [this, Matrix.transpose_map, hBp, hC]
    rfl

  have htr : ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
      (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map κ * (loc w (B.β (i + 1) j)).val))) := fun u => by
    unfold chart
    rw [hY, (hg 0 _).1]
  have hmu : ∀ u, (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
      (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) ((loc w (B.β i j)).valᵀ * ((spW₁ G i j).gram.map κ)ᵀ *
        u.map (fun a => cpt w (toEAf D a)) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (((loc w (B.β i (j + 1)))⁻¹).val)ᵀ (-(((loc w (B.β (i + 1) j))⁻¹).val)ᵀ)) := fun u => by
    unfold chart
    rw [hX, ← (hg (u.map fun a => cpt w (toEAf D a)) 0).2]
    rfl
  have hinc : ∀ x : D.host.E, cpt w (toEAf D (inclR (AF D.host.F) x)) = κ x := fun x => by
    rw [hκ]; exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hPl : ∀ k, colsEq t e w (e (.inl k)) ∈ Assignment.one.block _ _ := fun k => by
    rw [colsEq_inl]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hPr : ∀ k, colsEq t e w (e (.inr k)) ∉ Assignment.one.block _ _ := fun k hk => by
    rw [colsEq_inr] at hk; exact Bool.false_ne_true (Finset.mem_filter.1 hk).2

  have z₁ : ∀ z : AE D, GlobalTheory.EmbChart.idem (Bs.τ v) * z = z → cpt w (toEAf D (cA D z)) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have z₂ : ∀ z : AE D, cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * z = z → cpt w (toEAf D z) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have hat : ∀ (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) (b b' : AE D),
      b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b →
      b' * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b' →
      IsHalf b (u.submatrix id fun k => e (.inl k)) → IsHalf b' (u.submatrix id fun k => e (.inr k)) →
      At (evFin D.host.F v.1) u := fun u b b' hb hb' h1 h2 c hc => by
    have k1 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb h1 c hc
    have k2 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb' h2 c hc
    refine Matrix.ext fun a s => ?_
    obtain ⟨z, rfl⟩ := e.surjective s
    rcases z with k | k
    · exact congrFun₂ k1 a k
    · exact congrFun₂ k2 a k
  refine ⟨?_, fun u => by rw [htr, linB_ptB, hκ]⟩
  unfold IsMixChart
  simp only [htr, hmu]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : IsHalf (GlobalTheory.EmbChart.idem (Bs.τ v)) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h1 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h2 a k)
    exact ⟨hat u _ _ hb₁ hb₂ h1 h2, zero_inl e _ _ _ hPr _ _ _ _ hZ, zero_inr e _ _ _ hPl _ _ _ _ hU,
      eq_add_of_blocks e _ _ _ _ _ _ _ _ _ _ _ hZ hU (mixCoS_inl t e w B κ hinc u) (mixCoS_inr t e w B κ hinc u)⟩
  · have h1 : IsHalf (cA D (GlobalTheory.EmbChart.idem (Bs.τ v))) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    rw [Formalism.L2.Theta.cA_cA] at h2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h2 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h1 a k)
    exact ⟨hat u _ _ hb₂ hb₁ h1 h2, zero_inr e _ _ _ hPl _ _ _ _ hZ, zero_inl e _ _ _ hPr _ _ _ _ hU⟩

end GlobalTheory.TopFlip.ChartB
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_standing_triple_theta_first : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  first | exact @GlobalTheory.TopFlip.ChartB.exists_mixChart_linB | exact GlobalTheory.TopFlip.ChartB.exists_mixChart_linB | (intros; apply GlobalTheory.TopFlip.ChartB.exists_mixChart_linB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHalvesEqLinearModelLagrangians
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHalvesEqLinearModelLagrangians
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.SplitHalves

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie GlobalTheory.FlipMatch.RowChart

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem eq_zero_of_at {z : AE D} (hz : At (evFin D.host.F v) z) (h1 : piW τ z = 0)
    (h2 : piW (τ.comp D.sp.cm.sig) z = 0) : z = 0 := by
  classical
  set l : AF D.host.F := GlobalTheory.LatVac.liftV v 1 with hl
  have hz1 : z = l • z := by
    have h0 := hz (1 - l) (by rw [map_sub, map_one, hl, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [sub_smul, one_smul, sub_eq_zero] at h0
    exact h0
  refine ae_ext ?_ fun Q => ?_
  · have e : infPart D (algebraMap (AF D.host.F) (AE D) l) = 0 := by
      change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    rw [hz1, Algebra.smul_def, RingHom.map_mul, e, zero_mul, map_zero]
  · rw [map_zero, map_zero]
    by_cases h : Q.under (𝓞 D.host.F) = v
    · have hm : Q.asIdeal ∈ v.asIdeal.primesOver (𝓞 D.host.E) := ⟨Q.isPrime, ⟨h ▸ rfl⟩⟩
      rw [primesOver_eq_split (isCMExt_host D) τ] at hm
      rcases hm with e | e
      · obtain rfl : Q = splitPrime τ := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv τ, h1, map_zero]
      · obtain rfl : Q = splitPrime (τ.comp D.sp.cm.sig) := HeightOneSpectrum.ext e
        rw [← isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), h2, map_zero]
    · have e : cpt (D := D) Q (toEAf D (algebraMap (AF D.host.F) (AE D) l)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F Q (l.2 (Q.under (𝓞 D.host.F))) := (comp_toAd D).base l Q
      have e2 : l.2 (Q.under (𝓞 D.host.F)) = 0 := GlobalTheory.AdelicU.evalV_singleFin_ne h _
      rw [hz1, Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, e, e2, map_zero, zero_mul]

theorem mul_eq_iff {ε : AE D} (hε : At (evFin D.host.F v) ε) {p q : AE D →+* Fv D.host.F v} (hp : p ε = 1) (hq : q ε = 0)
    (hinj : ∀ z : AE D, At (evFin D.host.F v) z → p z = 0 → q z = 0 → z = 0) (z : AE D) :
    ε * z = z ↔ At (evFin D.host.F v) z ∧ q z = 0 := by
  refine ⟨fun h => ⟨fun a ha => ?_, ?_⟩, fun ⟨h1, h2⟩ => sub_eq_zero.1 (hinj _ (fun a ha => ?_) ?_ ?_)⟩
  · rw [← h, ← smul_mul_assoc, hε a ha, zero_mul]
  · rw [← h, RingHom.map_mul, hq, zero_mul]
  · rw [smul_sub, ← smul_mul_assoc, hε a ha, zero_mul, h1 a ha, sub_zero]
  · rw [RingHom.map_sub, RingHom.map_mul, hp, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_mul, h2, mul_zero, sub_zero]

theorem piW_atPl_one : piW τ (atPl (splitPrime τ) 1) = 1 := by
  classical
  exact (complEquiv τ (splitPrime_under τ)).injective (by
    rw [isPlaceIso_complEquiv τ, (atPl_spec _ _).2, Pi.single_eq_same, map_one])

theorem piW_comp_atPl_one : piW (τ.comp D.sp.cm.sig) (atPl (splitPrime τ) 1) = 0 := by
  classical
  exact (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
    rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec _ _).2,
      Pi.single_eq_of_ne (splitPrime_comp_ne (isCMExt_host D) τ), map_zero])

theorem isHalf_iff (ε : AE D) {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E) (hG : Gm.det ≠ 0)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    IsHalf ε (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔ ∀ a b, ε * u a b = u a b := by
  constructor
  · intro h a b
    have hAB : (Gm⁻¹).map (incA D) * Gm.map (incA D) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hG), Matrix.map_one _ (map_zero _) (map_one _)]
    obtain ⟨b, rfl⟩ := e.surjective b
    exact half_cancel (x := uᵀ.submatrix e id) hAB h b a
  · intro h a b
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← mul_assoc]
    exact congrArg (· * _) (h c (e a))

theorem entries_iff {m k : ℕ} (u : Matrix (Fin m) (Fin k) (AE D)) (q : AE D →+* Fv D.host.F v) :
    (∀ a b, At (evFin D.host.F v) (u a b) ∧ q (u a b) = 0) ↔ At (evFin D.host.F v) u ∧ u.map q = 0 :=
  ⟨fun h => ⟨fun c hc => Matrix.ext fun a b => (h a b).1 c hc, Matrix.ext fun a b => (h a b).2⟩,
    fun h a b => ⟨fun c hc => congrFun (congrFun (h.1 c hc) a) b, congrFun (congrFun h.2 a) b⟩⟩

theorem halves : ∀ {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∀ {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E), Gm.det ≠ 0 → ∀ u : Matrix (Fin m) (Fin k) (AE D),
      (IsHalf (atPl w 1) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ∧
      (IsHalf (cA D (atPl w 1)) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) := by
  intro D v τ w hw m k d e Gm hG u
  subst hw
  have hε := at_atPl τ 1
  constructor
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    exact forall₂_congr fun a b => mul_eq_iff hε (piW_atPl_one τ) (piW_comp_atPl_one τ)
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h1 h2) _
  · rw [isHalf_iff _ e Gm hG, ← entries_iff]
    refine forall₂_congr fun a b => mul_eq_iff (p := piW (τ.comp D.sp.cm.sig)) (at_cA hε) ?_ ?_
      (fun z h0 h1 h2 => eq_zero_of_at τ h0 h2 h1) _
    · rw [← piW_cA_eq, GlobalTheory.DualPairCheck.cA_cA, piW_atPl_one]
    · rw [piW_cA_eq, piW_comp_atPl_one]

end GlobalTheory.SplitHalves

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHalvesEqLinearModelLagrangiansStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians : ∀ {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∀ {m k d : ℕ} (e : Fin d ≃ Fin k) (Gm : Matrix (Fin m) (Fin m) D.host.E), Gm.det ≠ 0 → ∀ u : Matrix (Fin m) (Fin k) (AE D),
      (IsHalf (atPl w 1) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW (τ.comp D.sp.cm.sig)) = 0) ∧
      (IsHalf (cA D (atPl w 1)) (HMul.hMul (uᵀ.submatrix e id) (incM Gm) : Matrix (Fin d) (Fin m) (AE D)) ↔
        At (evFin D.host.F v) u ∧ u.map (piW τ) = 0) := by
  first | exact @GlobalTheory.SplitHalves.halves | exact GlobalTheory.SplitHalves.halves | (intros; apply GlobalTheory.SplitHalves.halves <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

namespace GlobalTheory.TopFlip

section Generic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {Y : Spc F E d} {M : Model σ X Y} {ψ : AddChar (AF F) ℂ} {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)}

theorem isLagrModel_chart {A A' B B' : Set (Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))} {Z Z' : Type} [TopologicalSpace Z] [Add Z]
    [TopologicalSpace Z'] [Add Z'] {co : _ → Z} {co' : _ → Z'} {ι} (h : IsLagrModel M ψ v A A' co ι) (Θ : Z ≃ₜ Z')
    (hΘ : ∀ x y, Θ (x + y) = Θ x + Θ y) (hB : B = A) (hB' : B' = A') (hco : ∀ u, Θ (co u) = co' u) :
    IsLagrModel M ψ v B B' co' (LinearMap.funLeft ℂ ℂ Θ.symm ∘ₗ ι) := by
  subst hB hB'
  refine ⟨(bijOn_funLeft Θ).comp h.1, fun u hu φ hφ φ₁ h₁ ha z => ?_, fun u hu φ hφ φ₁ h₁ ha x hx => ?_⟩
  · obtain ⟨z, rfl⟩ := Θ.surjective z
    rw [← hco, ← hΘ]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Homeomorph.symm_apply_apply]
    exact h.2.1 u hu φ hφ φ₁ h₁ ha z
  · rw [← hco]
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Homeomorph.symm_apply_apply]
    exact h.2.2 u hu φ hφ φ₁ h₁ ha x hx

end Generic

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A A' C : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype C] [DecidableEq C]

theorem smallP_smul [MeasurableSpace k] [BorelSpace k] (μ : Measure (GL A' k)) (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (c : ℂ)
    (Ψ : Matrix A' C k → ℂ) : smallP μ σ ν α (c • Ψ) = c • smallP μ σ ν α Ψ := by
  funext h
  simp only [smallP, smallF, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc c]
  rw [integral_const_mul]
  simp_rw [mul_assoc]
  ring

theorem smallP_haarVol [MeasurableSpace k] [BorelSpace k] {J : Subgroup (GL A' k)} (ho : IsOpen (J : Set (GL A' k)))
    (hK : J ≤ KO k A') (σ : A ⊕ A' ≃ C) (ν α : kˣ →* ℂˣ) (Ψ : Matrix A' C k → ℂ) :
    (haarVol (KO k A')).real J ≠ 0 ∧
      smallP (haarVol J) σ ν α Ψ = ((((haarVol (KO k A')).real J : ℝ) : ℂ))⁻¹ • smallP (haarVol (KO k A')) σ ν α Ψ := by
  obtain ⟨h0, h1⟩ := haar_ne_zero_ne_top (haarVol (KO k A')) ho hK
  have e : (haarVol (KO k A') J)⁻¹ • haarVol (KO k A') = haarVol J := by
    haveI : ((haarVol (KO k A') J)⁻¹ • haarVol (KO k A')).IsHaarMeasure :=
      Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.2 h1) (ENNReal.inv_ne_top.2 h0)
    exact eq_haarVol _ ho hK (by simp [ENNReal.inv_mul_cancel h0 h1])
  refine ⟨ENNReal.toReal_ne_zero.2 ⟨h0, h1⟩, ?_⟩
  funext h
  rw [← e]
  simp only [smallP, smallF, integral_smul_measure, Pi.smul_apply, smul_eq_mul, Complex.real_smul, ENNReal.toReal_inv,
    Measure.real, Complex.ofReal_inv]
  ring

theorem fourierSum_ind (ψ : AddChar k Circle) {ϖ : kˣ} (hϖ : IsUnif ϖ) (P : Finset C) (c : ℂ) :
    IsNatDatum ϖ 0 (c • Set.indicator {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} (1 : Matrix A C k → ℂ)) ∧
    fourierSum ψ ϖ 0 P (c • Set.indicator {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} 1) 0 = c := by
  constructor
  · have := (depthSpace (A := A) ϖ 0 (stdLat k C)).smul_mem c (hasDepth_indicator hϖ 0 (stdLat k C))
    have e : {Z : Matrix A C k | ∀ r s, Z r s ∈ (ValuativeRel.valuation k).integer} = (matLat A (GlobalTheory.SplitFlip.stdLat k C) : Set _) :=
      Set.ext fun Z => mem_matLat_stdLat.symm
    rw [e]
    exact this
  · haveI : Subsingleton (Res k 0) := Ideal.Quotient.subsingleton_iff.2 (by simp)
    haveI : Unique (A → P → Res k 0) := ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
    rw [fourierSum_apply, if_pos (by simp), Fintype.sum_unique, Pi.smul_apply, Set.indicator_of_mem]
    · simp [pairCols]
    · intro r s
      simp only [setCols, Matrix.of_apply]
      split_ifs
      · exact liftRes_mem _ _ _
      · exact zero_mem _

end Local

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}

theorem notMem_of_standing {t : T} (hst : SquareStanding G t) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := fun hmem => hst.2 w hw (by
  have e : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      (D.host.d : 𝓞 D.host.E) * ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) := by push_cast; ring
  rw [e]; exact Ideal.mul_mem_left _ _ hmem)


set_option maxHeartbeats 1000000 in
theorem local_charts (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (hst : SquareStanding G t)
    {e : Num G i j} {Bs : Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j} {X : Chars D.host.F D.host.E}
    {om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W} {om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W} (h : IsTripleOf W M t i j e Bs Γ X) {R Rf}
    (hm : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ X om om' R Rf) (hti : IsDoublyCompatible t i j e Bs Γ X) {w : Pl D.host.E} (hw : w ∈ locPl G t) :
    ∃ (ιA ι : ToA G t i j w) (ιB ι' : ToB G t i j w) (l : ℂ), l ≠ 0 ∧ IsLinModelA W B t e Γ w ιA ∧ IsLinModelB W B t e Γ w ιB ∧
      IsMixModelA W B t e Γ w ι ∧ IsMixModelB W B t e Γ w ι' ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum (unifAt w) m (ι φ) →
        ιA φ = fourierSum (psiAt W w)⁻¹ (unifAt w) m (Assignment.one.block _ _)ᶜ (ι φ)) ∧
      (∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ m, IsNatDatum (unifAt w) m (ι' φ) →
        ιB φ = fourierSum (psiAt W w) (unifAt w) m (Assignment.one.block _ _) (ι' φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _, ∀ c : ℂ, zetaA G t i j w (ιA φ) = c • zetaB G t i j w (ιB φ') →
        Rf.p _ φ = (l * c) • Rf.p' _ φ' := by
  classical
  set v := w.under (𝓞 D.host.F) with hv
  letI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv v
  haveI := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv v
  have hT := hm.triple
  have hvT : v ∈ X.T := (hti.1.2.2.1 v).2 ⟨w, hw, rfl⟩
  let v' : Bs.P := ⟨v, hT.chars.sub hvT⟩
  have hτ : splitPrime (Bs.τ v') = w := hti.1.2.2.2 v' w hw rfl
  obtain ⟨ιA, ιB, hA, hB, -, -, hz⟩ := hm.fin.zeta v' hvT
  obtain ⟨jj, j1, j2, j3, j4⟩ := GlobalTheory.T.exists_placeIso_reading_components_characters hL W t i j X h.α h.β (Bs.τ v') w hτ
  let C0 : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w) :=
    ⟨basCols B e w, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1)))⁻¹.val (-(loc w (B.β (i + 1) j))⁻¹.val),
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.mul_inv, Units.mul_inv, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one],
      by rw [basCols, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_mul, neg_mul_neg, Units.inv_mul, Units.inv_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk_one]⟩
  let cj := GeneralLinearGroup.map (jj : Fv D.host.F v →+* Kw w) (Γ.W.bas v)
  have hcc : (Γ.W.bas v).val.map jj * (cj⁻¹ * C0).val = basCols B e w := congrArg Units.val (mul_inv_cancel_left cj C0)
  generalize cj⁻¹ * C0 = cc at hcc
  obtain ⟨g, hg, cA', lA⟩ := GlobalTheory.T.exists_mixed_chart_through_W_coordinate hL W B t i j M hst e Bs Γ X om om' h hT hti.1 v' w hτ jj j1 j2 cc hcc
  obtain ⟨g', cB, lB⟩ := GlobalTheory.T.square_standing_triple_theta_first hL W B t i j M hst e Bs Γ X om om' h hT hti v' w hτ jj j1 j2 cc hcc
  have hb := notMem_of_standing hst hw
  have hS := (Good.isGood_of_notMem hL W hw hb).square i i.2 j j.2
  have hξ : (xiAt w)⁻¹ ≠ 0 := inv_ne_zero ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)
  have dW : Γ.W.J.det ≠ 0 := h.JWW ▸ det_skewGram_ne _ _ e
  have dV : Γ.V.J.det ≠ 0 := by rw [h.JW, one_smul]; exact GlobalTheory.RouteCoords.gram_det_ne _
  have dV' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (GlobalTheory.RouteCoords.gram_det_ne _)
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd W.ψ := h.ψ ▸ hT.base.std
  rw [h.ψ] at hA hB
  obtain ⟨ι, i1, i2⟩ := exists_mixed (M := Γ.M) (ψ := W.ψ) hS.unif hS.cond j2 hξ j4 (h := invT cc) cA' hA.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew dV dW Γ.M W.ψ hstd _ _ _ u hu h0
      φ hφ φ₁ h₁ ha).1 ιA hA)
    fun x u hx hu => GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V Γ.W hT.geo.hV.herm hT.geo.hW.skew W.ψ _ _ _ x u hx hu
  obtain ⟨ι', k1, k2⟩ := exists_mixed (M := Γ.M') (ψ := W.ψ) hS.unif hS.inv.cond j2 hξ (χ := fun x => psiLoc W.ψ v (-x))
    (fun x => by rw [j4, AddChar.inv_apply, map_neg, mul_neg]) cB hB.bij
    (fun u hu h0 φ hφ φ₁ h₁ ha => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew dV' dW Γ.M' W.ψ hstd _ _ _ u hu
      ((pairM_comm _ _).trans h0) φ hφ φ₁ h₁ ha).2 ιB hB)
    fun x u hx hu => by
      rw [GlobalTheory.T.tensorSymplecticForm_at_split_finite_place hT.base.cm Γ.V' Γ.W hT.geo.hV'.herm hT.geo.hW.skew W.ψ (Bs.τ v') (Γ.V'.bas v) (Γ.W.bas v) x u hx hu, neg_sub]
  haveI := isHaarMeasure_haarVol (k := Kw w) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI := isHaarMeasure_haarVol (k := Kw w) (n := Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) isOpen_KO le_rfl
  haveI := isHaarMeasure_haarVol (k := Fv D.host.F v) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI : @MeasureTheory.Measure.IsHaarMeasure (GL (Fin (spW₁ G i j).rank) (Kw w)) _ _
      (@Units.instMeasurableSpace (Matrix (Fin (spW₁ G i j).rank) (Fin (spW₁ G i j).rank) (Kw w)) _
        GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
      (haarVol (KO (Kw w) (Fin (spW₁ G i j).rank))) :=
    isHaarMeasure_haarVol (k := Kw w) (n := Fin (spW₁ G i j).rank) isOpen_KO le_rfl
  haveI : @MeasureTheory.Measure.IsHaarMeasure (GL (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Kw w)) _ _
      (@Units.instMeasurableSpace (Matrix (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) (Kw w)) _
        GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix)
      (haarVol (KO (Kw w) (Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))))) :=
    isHaarMeasure_haarVol (k := Kw w) (n := Fin ((locGrid G t w).rank ((i : ℕ), (j : ℕ)))) isOpen_KO le_rfl
  obtain ⟨l₂, hl₂, z₂⟩ := GlobalTheory.T.zetaIdentity_persists_row_column_changes (Kw w) _ _ (rankW G t i j w) _ _ _ _ (finCongr (rankW₁ G t i j w)) (colsEq t e w) finSumFinEquiv
    (stdSplit ((locGrid G t w).rank_square i j)) (haarVol (KO (Kw w) _)) (haarVol (KO (Kw w) _))
    (unifAt w) ((locGrid G t w).nu i j) 1 g g' cc hg
  obtain ⟨l₁, hl₁, z₁⟩ := GlobalTheory.T.zetaIdentity_transport_localFieldIso (Fv D.host.F v) (Kw w) jj j2 (spW G i j).rank (Fin (spW₁ G i j).rank) _ finSumFinEquiv
    (haarVol (KO _ _)) (haarVol (KO _ _)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v) (unifAt w) (exists_isUnif (k := Fv D.host.F v)).choose_spec
    hS.unif (chrW X.ν (Bs.τ v')) (chrW X.β (Bs.τ v')) _ 1 j3
  obtain ⟨ΘA, hΘA⟩ := exists_homeo jj (finCongr (rankW G t i j w)) (colsEq t e w) g (invT cc) j2.1 j2.2.1
  obtain ⟨ΘB, hΘB⟩ := exists_homeo jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g' cc j2.1 j2.2.1
  have hfA := GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians (Bs.τ v') w hτ (e.symm.trans finSumFinEquiv).symm _
    (GlobalTheory.RouteCoords.gram_det_ne (GlobalTheory.Grid.sgn true (spW G i j)))
  have hfB := GlobalTheory.T.splitPlace_halves_eq_linear_model_lagrangians (Bs.τ v') w hτ (e.symm.trans finSumFinEquiv).symm _ (GlobalTheory.RouteCoords.gram_det_ne (spW₁ G i j))
  have eA : ∀ φ Z, (LinearMap.funLeft ℂ ℂ ΘA.symm ∘ₗ ιA) φ (ΘA Z) = ιA φ Z := fun φ Z => congrArg (ιA φ) (ΘA.symm_apply_apply Z)
  have eB : ∀ φ Z, (LinearMap.funLeft ℂ ℂ ΘB.symm ∘ₗ ιB) φ (ΘB Z) = ιB φ Z := fun φ Z => congrArg (ιB φ) (ΘB.symm_apply_apply Z)
  refine ⟨LinearMap.funLeft ℂ ℂ ΘA.symm ∘ₗ ιA, ι, LinearMap.funLeft ℂ ℂ ΘB.symm ∘ₗ ιB, ι', l₁ * l₂, mul_ne_zero hl₁ hl₂,
    isLagrModel_chart (isLagrModel_of_isLin hA) ΘA (fun x y => by rw [hΘA, hΘA, hΘA, chart_add])
      (Set.ext fun u => (hfA u).1) (Set.ext fun u => (hfA u).2) fun u => (hΘA _).trans (lA u),
    isLagrModel_chart (isLagrModel_of_isLin hB) ΘB (fun x y => by rw [hΘB, hΘB, hΘB, chart_add])
      (Set.ext fun u => (hfB u).2) (Set.ext fun u => (hfB u).1) fun u => (hΘB _).trans (lB u),
    i1, k1, fun φ hφ m hm => funext fun S => ?_, fun φ hφ m hm => funext fun S => ?_, fun φ hφ φ' hφ' c hc => ?_⟩
  · obtain ⟨Z, rfl⟩ := ΘA.surjective S
    rw [eA, i2 φ hφ m hm, hΘA]
  · obtain ⟨Z, rfl⟩ := ΘB.surjective S
    rw [eB, k2 φ hφ m hm, hΘB, inv_inv]
  · have e6 : chrW X.α (Bs.τ v') = chrW X.ν (Bs.τ v') * chrW X.β (Bs.τ v') := by
      ext x
      simp [chrW, GlobalTheory.LFun.locChar, Chars.ν]
    rw [← map_smul]
    refine (hz φ hφ _ (Submodule.smul_mem _ _ hφ')).2 ?_
    rw [e6]
    rw [zetaA, zetaB, ← smallP_smul] at hc
    have := z₁ _ _ (z₂ _ _ hc)
    convert this using 2
    · funext Z
      rw [← eA, hΘA]
      rfl
    · funext Y
      rw [map_smul, Pi.smul_apply, ← eB, hΘB, smul_eq_mul, mul_assoc, mul_assoc]
      rfl

theorem zeta_flip (hL : L.Is μ₀) (W : G.Weil) {t : T} (i j : Fin D.R.m) (hst : SquareStanding G t) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) : levVol G t i j w ≠ 0 ∧ ∀ n Φ, depthAt G w ≤ n → IsNatDatum (unifAt w) n Φ →
      zetaA G t i j w (fourierSum (psiAt W w)⁻¹ (unifAt w) n (Assignment.one.block _ _)ᶜ (flipAt W t i j w n Φ)) =
        ((levVol G t i j w : ℝ) : ℂ)⁻¹ • zetaB G t i j w (fourierSum (psiAt W w) (unifAt w) n (Assignment.one.block _ _) Φ) := by
  have hS := (Good.isGood_of_notMem hL W hw (notMem_of_standing hst hw)).square i i.2 j j.2
  have h1 := GivenAdm.givenLevel_open hL hw ((i : ℕ), (j : ℕ))
  have h2 := isOpen_map_invT h1.1 h1.2
  haveI hμ := isHaarMeasure_haarVol h2.1 h2.2
  have key := smallP_haarVol h2.1 h2.2 (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1)
  refine ⟨(key 0).1, fun n Φ hn hΦ => ?_⟩
  rw [flipAt, squareFlip, GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth _ _ _ _ _ _ _ hS.unif hS.inv.cond _ (by
    rw [← latA_blockLat, ← Grid.alpha_div_beta]
    exact GlobalTheory.FrameDepth.hasDepth_phiA _ _ _ _ _ (hμ := hμ) _ _ _ _ _ _ hS.unif (hS.one_le.trans hn) (LocTensor.condLE_mono hS.unif hn hS.condν)
      (GlobalTheory.SplitFlip.FourierDepth.hasDepth_fourierSum hS.unif hS.cond n _ hΦ))]
  exact (GlobalTheory.T.primitiveFrameDatum_zetaIntegral_eq_smaller (Kw w) _ _ _ _ _ _ 1 _ n _ _ hS.unif).trans (key _).2

theorem zeta_std (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) {i j : Fin D.R.m} (X : TriG G i j) (hst : ∀ t, SquareStanding G t)
    (hA : IsFrame X.rA.β (G.Λ (.grid (i + 1) (j + 1)))) (hA' : IsFrame X.rA'.β (G.Λ (.grid i j))) (hX : IsFrame X.rW.β (latX G i j)) :
    ∃ x : ∀ w : Pl D.host.E, (Kw w)ˣ, ∀ t, ∀ w ∈ locPl G t, ValuativeRel.valuation (Kw w) (x w : Kw w) = 1 ∧
      locFst B t X w ∈ GlobalTheory.WeilM.SB _ ∧ locSnd B t X w ∈ GlobalTheory.WeilM.SB _ ∧
      zetaA G t i j w (locFst B t X w) = (((locGrid G t w).nu i j (x w) : ℂˣ) : ℂ) • zetaB G t i j w (locSnd B t X w) := by
  have H : ∀ w : Pl D.host.E, ∃ x : (Kw w)ˣ, ∀ t, w ∈ locPl G t → ValuativeRel.valuation (Kw w) (x : Kw w) = 1 ∧
      zetaA G t i j w (locFst B t X w) = (((locGrid G t w).nu i j x : ℂˣ) : ℂ) • zetaB G t i j w (locSnd B t X w) := fun w => by
    by_cases hex : ∃ t, w ∈ locPl G t
    swap
    · exact ⟨1, fun t ht => absurd ⟨t, ht⟩ hex⟩
    obtain ⟨t₀, ht₀⟩ := hex
    obtain ⟨a1, a2, a3⟩ := GlobalTheory.T.grid_frame_local_compact_membership hL B t₀ i j X (hst t₀) hA hA' hX w ht₀
    obtain ⟨x, hx, hz⟩ := GlobalTheory.T.bigZetaIntegral_eq_smul_smallZetaIntegral_of_integralChange (Kw w) _ _ _ _ (ordX G t₀ i j w) (stdSplit ((locGrid G t₀ w).rank_square i j)) finSumFinEquiv
      _ _ _ a1 a2 a3
    exact ⟨x, fun t _ => ⟨hx, hz (unifAt w) ((locGrid G t w).nu i j) 1 _ _
      (GlobalTheory.T.zetaIntegral_standardPair_first_eq_second (Kw w) ((locGrid G t w).nu i j) 1 (unifAt w) (X.c t w) _ _ (isUnif_unifAt w))⟩⟩
  choose x hx using H
  refine ⟨x, fun t w hw => ?_⟩
  have hS := (Good.isGood_of_notMem hL W hw (notMem_of_standing (hst t) hw)).square i i.2 j j.2
  obtain ⟨s1, s2⟩ := GlobalTheory.T.standardPair_mem_schwartzBruhat_of_conductorExponentLE (Kw w) ((locGrid G t w).nu i j) (unifAt w) _ (X.c t w) ((locGrid G t w).rank (i + 1, j + 1)) ((locGrid G t w).rank (i, j))
    hS.unif (by rw [← Grid.alpha_div_beta]; exact hS.condν)
  obtain ⟨ΘA, hΘA⟩ := exists_homeo (RingEquiv.refl (Kw w)) (Equiv.refl _) (ordX G t i j w) (chA B t X w) (invT (chX B t X w))
    continuous_id continuous_id
  obtain ⟨ΘB, hΘB⟩ := exists_homeo (RingEquiv.refl (Kw w)) (Equiv.refl _) (ordX G t i j w) (chB B t X w) (chX B t X w)
    continuous_id continuous_id
  refine ⟨(hx w t hw).1, ?_, ?_, (hx w t hw).2⟩
  · have : locFst B t X w = GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _ ∘ ΘA :=
      funext fun Z => by rw [Function.comp_apply, hΘA]; rfl
    rw [this]
    exact ⟨s1.1.comp_continuous ΘA.continuous, s1.2.comp_homeomorph ΘA⟩
  · have : locSnd B t X w = GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _ ∘ ΘB :=
      funext fun Z => by rw [Function.comp_apply, hΘB]; rfl
    rw [this]
    exact ⟨s2.1.comp_continuous ΘB.continuous, s2.2.comp_homeomorph ΘB⟩

end GlobalTheory.TopFlip

end
