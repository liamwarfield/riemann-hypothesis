module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalDatumThetaFactorsPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatchAtType
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AtMostOneHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIdemSumLeft
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.StdMatch
open GlobalTheory.LocMod GlobalTheory.SymBridge GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem latO_le (S T : HSp D) (LS LT) {p q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, p v → q v) : latO S T LS LT p ≤ latO S T LS LT q :=
  AddSubgroup.closure_mono fun _ ⟨α, h1, h2, h3⟩ => ⟨α, h1, fun v hv => h2 v fun hp => hv (h v hp), h3⟩

theorem mem_latO_at (q : GlobalTheory.FinPl.SplitPt D k) {S T : HSp D} {LS LT} {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True)
    (hh : IsHalf q.e u) : u ∈ latO S T LS LT (· = q.v) := by
  obtain ⟨ε, ⟨β, rfl, h1, h0⟩, hsum⟩ := q.above
  have hβ : β ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have main : (latO S T LS LT fun _ => True) ≤ (latO S T LS LT (· = q.v)).comap
      (DistribSMul.toAddMonoidHom (WO S T) (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β))) := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩
    refine AddSubgroup.subset_closure ⟨β * α, fun v => by rw [map_mul]; exact mul_mem (hβ v) (hα v), fun v hv => ?_,
      a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 v hv, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Matrix.of_apply]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  have h := main hu
  rw [AddSubgroup.mem_comap] at h
  convert h using 1
  ext i j
  change _ = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) * u i j
  rw [← hsum, ← hh i j, ← mul_assoc, add_mul, q.split.1, mul_comm (cA D q.e), q.split.2.1, add_zero]

theorem int_iff_up_mem (q : GlobalTheory.FinPl.SplitPt D k) (hq : q.UnitAA) {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    {S T : HSp D} (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) (eS : (LS : Set (Fin S.rank → D.host.E)) = intVec D S.rank)
    (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFS : ∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v))
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v))
    (x : Matrix Y Y' k) : (∀ r s, x r s ∈ 𝒪[k]) ↔ (ofSplit q).up FS FT x ∈ stdHom S T := by
  rw [stdHom, ← eS, ← eT]
  refine ⟨fun hx => latO_le S T _ _ (fun _ _ => trivial) (GlobalTheory.UpMem.up_mem_latO D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT x hx),
    fun hx => ?_⟩
  have hh := Witness.up_half (ofSplit q) FS FT x
  obtain ⟨x', hx', e⟩ := GlobalTheory.HalfIntUp.exists_int_up D k q hq Y Y' S T FS FT LS LT hS hT hFS hFT _ (mem_latO_at q hx hh) hh
  have := congrArg ((ofSplit q).down FS FT) e
  rw [Witness.down_up, Witness.down_up] at this
  rwa [this]

theorem gamma_int (q : GlobalTheory.FinPl.SplitPt D k) {Y : Type} [Fintype Y] [DecidableEq Y] {T : HSp D} (FT : Frame k T.rank Y)
    {LT : GlobalTheory.FinPl.Lat T} (eT : (LT : Set (Fin T.rank → D.host.E)) = intVec D T.rank)
    (hFT : ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) (r s) :
    FT.γ r s ∈ 𝒪[k] := by
  refine (hFT fun r => FT.γ r s).2 ?_ r
  have hs : (Pi.single s 1 : Fin T.rank → D.host.E) ∈ LT := by
    rw [← SetLike.mem_coe, eT]
    intro i
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  convert GlobalTheory.UpMem.e_mul_mem_latV q T LT hs using 2 with i
  have : (FT.β *ᵥ fun r => FT.γ r s) i = (FT.β * FT.γ) i s := rfl
  rw [this, FT.βγ, ← q.sec_pr, Matrix.one_apply, Pi.single_apply]
  split_ifs <;> simp

theorem mk_eq_mk_of_int {n : Type} {x y : n → k} (h : ∀ c, y c - x c ∈ 𝒪[k]) :
    (Submodule.Quotient.mk x : _ ⧸ box n (1 : kˣ)) = Submodule.Quotient.mk y :=
  ((Submodule.Quotient.eq _).2 (show y - x ∈ box n (1 : kˣ) from fun c => h c)).symm

end Gen

section Mat
variable {E k : Type} [Field E] [NumberField E] [StarRing E] [Field k]

theorem mul_toLoc (ι : E →+* k) {Y Y' : Type} [Fintype Y] [Fintype Y'] {a b nS nT : ℕ} (hS : nS = a) (hT : nT = b)
    (f : (Fin a → E) ≃ₗ[E] (Fin a → E)) (f' : (Fin b → E) ≃ₗ[E] (Fin b → E)) (e' : Y' ≃ Fin a) (e : Y ≃ Fin b)
    (β : Matrix (Fin nS) Y' k) (M : Matrix (Fin nT) Y k) (hβ : ∀ r c, β r c = ι (f (Pi.single (e' c) 1) (finCongr hS r)))
    (hM : ∀ r c, M r c = ι (f' (Pi.single (e c) 1) (finCongr hT r))) (γ : Matrix (Fin nT) (Fin nS) E) :
    M * toLoc ι e e' (Formalism.L2.Col.inFr f f' (Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS)))) = γ.map ι * β := by
  subst hS hT
  ext r c
  have key : ∀ x : Fin nT → E, ∑ y : Y, f' (Pi.single (e y) 1) r * x (e y) = f' x r := fun x => by
    rw [e.sum_comp fun j => f' (Pi.single j 1) r * x j]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [pi_eq_sum_univ' x, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, hβ, hM, toLoc, Matrix.map_apply, ← map_mul, ← map_sum, finCongr_refl, Equiv.refl_apply]
  rw [key]
  simp [Formalism.L2.Col.inFr, Matrix.mulVec, dotProduct]

end Mat

theorem twSt_h {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel) {S₀ : Set ℕ}
    (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (m2 j : ℕ)
    (al : (Formalism.L2.Col.twSt Ch sel mu cst m2 j).β) (P : Formalism.L2.Col.rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs) :
    (Formalism.L2.Col.twSt Ch sel mu cst m2 j).h al P = 1 := by
  revert al
  cases j with
  | zero => exact fun _ => rfl
  | succ i =>
    rw [Formalism.L2.Col.twSt]
    by_cases h1 : i + 1 ≤ m2
    · rw [if_pos h1]
      exact fun _ => dif_neg fun h => (@Finset.mem_sdiff _ (_) _ _ _).1 h |>.2 hP
    · rw [if_neg h1]
      by_cases h2 : i + 1 = m2 + 1
      · rw [if_pos h2]
        exact fun _ => rfl
      · rw [if_neg h2]
        exact fun al => al.elim

section World
open _root_.Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {v : B.Word} {Ch : ℕ → Type}
  {A : ColDat I l Z v Ch} {a : XPart (I.rec7 l Z) v} {ζ₀ : Fin a.Lz.rank → (I.rec7 l Z).host.E}
  {PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E} {G : GX a ζ₀ PP} {P : rowSG (B.primes X) I.sel (I.tup I.mu0)}



end World

section Main
open _root_.Formalism.L2.Col

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {w : World I l Z} {v : B.Word}
  {a : XPart (I.rec7 l Z) v} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {o : OffX a k ((B.primes X).vT v)} {G : ∀ PP : a.c.Pg, GX a o.ζ₀ PP.1} {A : ColDat I l Z v (w.C.herm.base.Ch v)}

end Main

end GlobalTheory.SeeSaw.StdMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.UnitLocLastRow

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_tmul (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) (y : v.adicCompletion F) :
    Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] y) = σ e ⊗ₜ[F] y := by
  simp [Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]

theorem sigR_inclE (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) e) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (σ e) := by
  show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) = σ e ⊗ₜ[F] 1
  exact sigR_tmul σ v e 1

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F))
    (a : E ⊗[F] v.adicCompletion F) : Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.sigR σ (v.adicCompletion F) a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul e y => rw [sigR_tmul, sigR_tmul, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_mem_intV (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) {a : E ⊗[F] v.adicCompletion F}
    (ha : a ∈ Formalism.BasicNotions.intV E v) : Formalism.UG.sigR σ (v.adicCompletion F) a ∈ Formalism.BasicNotions.intV E v := by
  have h : Formalism.BasicNotions.intV E v ≤ (Formalism.BasicNotions.intV E v).comap (Formalism.UG.sigR σ (v.adicCompletion F)) := by
    show Subring.closure _ ≤ _
    rw [Subring.closure_le]
    rintro _ (⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · show Formalism.UG.sigR σ (v.adicCompletion F) (e ⊗ₜ[F] 1) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul]
      apply Subring.subset_closure
      left
      exact ⟨⟨σ e, GlobalTheory.uLocDual_intOE_map (σ : E →+* E) he⟩, rfl⟩
    · show Formalism.UG.sigR σ (v.adicCompletion F) (1 ⊗ₜ[F] y) ∈ Formalism.BasicNotions.intV E v
      rw [sigR_tmul, map_one]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, rfl⟩
  exact h ha

theorem inclE_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 E) :
    Formalism.UG.inclE (F := F) (v.adicCompletion F) (r : E) ∈ Formalism.BasicNotions.intV E v :=
  Formalism.UG.P.easyc_inclE_mem (F := F) (v.adicCompletion F) (v.adicCompletionIntegers F).toSubring _ ⟨r, rfl⟩

theorem one_int (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (a b : Fin n) :
    (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈ Formalism.BasicNotions.intV E v := by
  rw [Matrix.one_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem mulVec_mem_dLat (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} [NeZero n] (p : 𝓞 E) (hp0 : (p : E) ≠ 0)
    (N : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (hN : ∀ i j, N i j ∈ Formalism.BasicNotions.intV E v)
    (hlast : ∀ j, ∃ c ∈ Formalism.BasicNotions.intV E v, N (Formalism.L2.Col.lastIdx n) j - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c)
    (y : Fin n → E ⊗[F] v.adicCompletion F)
    (hy : y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹))) :
    N *ᵥ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) (Formalism.L2.Col.rll_dLat n ((p : E)⁻¹)) := by
  have key := Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0)
  obtain ⟨h1, h2⟩ := (key y).1 hy
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have hyint : ∀ j, y j ∈ Formalism.BasicNotions.intV E v := by
    intro j
    by_cases hj : j = Formalism.L2.Col.lastIdx n
    · rw [hj]
      have e : y (Formalism.L2.Col.lastIdx n) = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
          (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n)) := by
        rw [← mul_assoc, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E)), hPinv, one_mul]
      rw [e]
      exact mul_mem (inclE_int v p) h2
    · exact h1 j hj
  refine (key _).2 ⟨fun i _ => ?_, ?_⟩
  · show ∑ j, N i j * y j ∈ Formalism.BasicNotions.intV E v
    exact sum_mem fun j _ => mul_mem (hN i j) (hyint j)
  · choose c hc hcl using hlast
    have e : (N *ᵥ y) (Formalism.L2.Col.lastIdx n) = ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) (Formalism.L2.Col.lastIdx n) +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * ∑ j, c j * y j := by
      show ∑ j, N _ j * y j = ∑ j, (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) _ j * y j + _
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show N (Formalism.L2.Col.lastIdx n) j = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) j +
        Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c j by rw [← hcl j]; ring]
      ring
    rw [e, Matrix.one_mulVec, mul_add, ← mul_assoc, hPinv, one_mul]
    exact add_mem h2 (sum_mem fun j _ => mul_mem (hc j) (hyint j))

theorem mem_Uloc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ hσ n _ J hJ T f bad S p q hq hpq hcop hT hL v hv x hU hint hlast
  subst hJ
  have hTE : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have hp0 : (p : E) ≠ 0 := left_ne_zero_of_mul (hpq ▸ hTE)
  have hq0 : (q : E) ≠ 0 := right_ne_zero_of_mul (hpq ▸ hTE)
  have hPinv : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hp0, map_one]
  have h0 : Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) *
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      (1 : Matrix (Fin n) (Fin n) E).map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := hU
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h0
  have hMi : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) =
      Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
    calc ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
        = (Formalism.UG.cT (Formalism.UG.sigR σ (v.adicCompletion F)) (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *
          (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) *
          ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) := by
          rw [h0, Matrix.one_mul]
      _ = _ := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hMient : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b =
      Formalism.UG.sigR σ (v.adicCompletion F) ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a) := by
    intro a b; rw [hMi]; rfl
  have hMiint : ∀ a b, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b ∈
      Formalism.BasicNotions.intV E v := by
    intro a b; rw [hMient]; exact sigR_mem_intV σ v (hint b a)
  choose c hc hcl using hlast
  have hmat : ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1 =
      -(((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))) := by
    rw [Matrix.sub_mul, Units.mul_inv, Matrix.one_mul]; abel
  have hMilast : ∀ i, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) *
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h1 := congrFun (congrFun hmat (Formalism.L2.Col.lastIdx n)) i
    rw [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply] at h1
    rw [h1, mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.sub_apply, hcl k, mul_assoc]
  have hMilastI : ∀ i, ∃ e ∈ Formalism.BasicNotions.intV E v,
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F))
      (Formalism.L2.Col.lastIdx n) i - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) i =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * e :=
    fun i => ⟨_, neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)), hMilast i⟩
  have hs1 : ∀ a b, Formalism.UG.sigR σ (v.adicCompletion F) ((1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) a b) =
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) b a := by
    intro a b
    by_cases hab : a = b
    · subst hab; rw [Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab), map_zero]
  have hcol : ∀ i, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) -
      (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i (Formalism.L2.Col.lastIdx n) =
      Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * Formalism.UG.sigR σ (v.adicCompletion F)
        (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k i) := by
    intro i
    have h := congrArg (Formalism.UG.sigR σ (v.adicCompletion F)) (hMilast i)
    rw [map_sub, map_mul, hMient, sigR_sigR σ hσ v, sigR_inclE, ← hq, hs1] at h
    exact h

  have h1 : x ∈ Formalism.UG.levelVL σ (1 : Matrix (Fin n) (Fin n) E) v S.Lb := by
    rw [hL]
    refine Subgroup.mem_inf.2 ⟨hU, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
    · exact mulVec_mem_dLat v p hp0 _ hint (fun j => ⟨c j, hc j, hcl j⟩) y hy
    · have := mulVec_mem_dLat v p hp0 _ hMiint hMilastI _ hy
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

  have h2 : ∀ y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v)
      (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈
        Formalism.UG.latS (F := F) (v.adicCompletion F) (Formalism.BasicNotions.intV E v) S.Lb := by
    intro y hy
    rw [hL, GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq] at hy
    rw [hL]
    obtain ⟨hy1, hy2⟩ := (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v (q : E) hq0 y).1 hy
    rw [show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y =
      ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) *ᵥ y by rw [Matrix.sub_mulVec, Matrix.one_mulVec]]
    refine (Formalism.L2.Col.rll_mem_loc_dLat (F := F) n v ((p : E)⁻¹) (inv_ne_zero hp0) _).2 ⟨fun i _ => ?_, ?_⟩
    · show ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) i j * y j ∈ Formalism.BasicNotions.intV E v
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj, Matrix.sub_apply, hcol i, mul_comm (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E)), mul_assoc]
        exact mul_mem (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k i)))) hy2
      · exact mul_mem (sub_mem (hint i j) (one_int v i j)) (hy1 j hj)
    · show Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
        ∑ j, ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) j * y j ∈ Formalism.BasicNotions.intV E v
      rw [Finset.mul_sum]
      refine sum_mem fun j _ => ?_
      by_cases hj : j = Formalism.L2.Col.lastIdx n
      · rw [hj]
        obtain ⟨a, b, hab⟩ := hcop
        have hE : (a : E) * (p : E) + (b : E) * (q : E) = 1 := by
          exact_mod_cast congrArg (fun r : 𝓞 E => (r : E)) hab
        have hab' : Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) +
            Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) = 1 := by
          have h := congrArg (Formalism.UG.inclE (F := F) (v.adicCompletion F)) hE
          rwa [map_add, map_mul, map_mul, map_one] at h
        have hDc := hcl (Formalism.L2.Col.lastIdx n)
        have hDd := hcol (Formalism.L2.Col.lastIdx n)
        rw [← Matrix.sub_apply] at hDc hDd
        have e : Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) *
            (((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) - 1) (Formalism.L2.Col.lastIdx n) (Formalism.L2.Col.lastIdx n) *
              y (Formalism.L2.Col.lastIdx n)) =
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * Formalism.UG.sigR σ (v.adicCompletion F)
              (-∑ k, c k * ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) k
                (Formalism.L2.Col.lastIdx n)) +
             Formalism.UG.inclE (F := F) (v.adicCompletion F) (b : E) * c (Formalism.L2.Col.lastIdx n)) *
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (q : E) * y (Formalism.L2.Col.lastIdx n)) := by
          linear_combination (Formalism.UG.inclE (F := F) (v.adicCompletion F) ((p : E)⁻¹) * y (Formalism.L2.Col.lastIdx n) -
              Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDc +
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hPinv +
            (Formalism.UG.inclE (F := F) (v.adicCompletion F) (a : E) * y (Formalism.L2.Col.lastIdx n)) * hDd -
            (c (Formalism.L2.Col.lastIdx n) * y (Formalism.L2.Col.lastIdx n)) * hab'
        rw [e]
        exact mul_mem (add_mem (mul_mem (inclE_int v a)
          (sigR_mem_intV σ v (neg_mem (sum_mem fun k _ => mul_mem (hc k) (hMiint k _)))))
          (mul_mem (inclE_int v b) (hc _))) hy2
      · rw [Matrix.sub_apply, hcl j, ← mul_assoc, ← mul_assoc, hPinv, one_mul]
        exact mul_mem (hc j) (hy1 j hj)
  exact GlobalTheory.uloc_of_triv_disc σ S v hv x h1 h2

end GlobalTheory.UnitLocLastRow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.UnitLocLastRow.mem_Uloc | exact GlobalTheory.UnitLocLastRow.mem_Uloc | (intros; apply GlobalTheory.UnitLocLastRow.mem_Uloc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixEntryIntegralityCongruence
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.TraceBwd

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge GlobalTheory.RootEx

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colGroup_of_embX {s κ τ : ℕ} (S : SymData k s κ) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : embX (s + 1) g ∈ ((S.T (Fin τ)).lev 0 (s + 1) (Nat.zero_add _)).J) : g ∈ colGroup k κ (Fin τ) := by
  obtain ⟨h1, -, -⟩ := GlobalTheory.FirstVertexFrame.firstVertex_typeChain k S.ψ S.ϖ s (Fin τ) κ S.P
    (GlobalTheory.SymShape.sym_shape _ _ _ _ _ _ _ S.sym) S.μ S.tame (s + 1) (Nat.zero_add _)
  rw [← h1]
  refine ⟨1, one_mem _, mem_Cgrp.2 ⟨?_, ?_⟩⟩
  · rw [one_mul]
    exact (le_sup_left : (embX (s + 1)).range ≤ R k _ (s + 1) 1) ⟨g, rfl⟩
  · rw [inv_one, one_mul, mul_one, one_mul]
    exact hg

theorem entries_of_colGroup {κ τ n : ℕ} (e : XIx (Fin κ) (Fin τ) 0 ≃ Fin n) (he : IsOrd xPos e) (g : GL (XIx (Fin κ) (Fin τ) 0) k)
    (hg : g ∈ colGroup k κ (Fin τ)) (a b : XIx (Fin κ) (Fin τ) 0) :
    g.val a b ∈ 𝒪[k] ∧ (e b ≤ e a → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1) := by
  have hp : ∀ c, colPos κ (Fin τ) c = (e c).val := fun c => by
    rw [he c]
    rcases c with (c | c) | c
    exacts [rfl, c.elim0, c.1.elim0]
  obtain ⟨_, ⟨g₀, rfl, rfl⟩, hu⟩ := hg
  refine ⟨(g₀.val a b).2, fun hab => ?_⟩
  have h1 : residue 𝒪[k] (g₀.val a b) = (1 : Matrix _ _ 𝓀[k]) a b := hu a b (by rw [hp, hp]; exact hab)
  have h2 : (1 : Matrix _ _ 𝓀[k]) a b = residue 𝒪[k] ((1 : Matrix _ _ 𝒪[k]) a b) := by
    simp only [Matrix.one_apply, apply_ite (residue 𝒪[k]), map_one, map_zero]
  rw [h2, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff] at h1
  have h3 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 h1
  convert h3 using 2
  simp only [Matrix.one_apply]
  split_ifs <;> rfl

theorem exists_mat {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y]
    (F : Frame k V.rank Y) (e : Y ≃ Fin V.rank) (hβ : F.β = (1 : Matrix (Fin V.rank) (Fin V.rank) k).submatrix id e) (x : GA D V) :
    ∃ g : GL Y k, (mt V x).map q.pr = F.β * g.val * F.γ ∧ ∀ a b, g.val a b = (mt V x).map q.pr (e a) (e b) := by
  have hmul : ∀ y z : GA D V, y * z = 1 → (F.γ * (mt V y).map q.pr * F.β) * (F.γ * (mt V z).map q.pr * F.β) = 1 := fun y z h => by
    have h1 : mt V y * mt V z = 1 := by
      have h2 : mt V y * mt V z = mt V (y * z) := rfl
      rw [h2, h]
      rfl
    have h3 : (mt V y).map q.pr * (mt V z).map q.pr = 1 := by
      rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
    calc _ = F.γ * ((mt V y).map q.pr * (F.β * F.γ) * (mt V z).map q.pr) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h3, Matrix.mul_one, F.γβ]
  let g : GL Y k := ⟨_, _, hmul x x⁻¹ (mul_inv_cancel x), hmul x⁻¹ x (inv_mul_cancel x)⟩
  have hg : (mt V x).map q.pr = F.β * g.val * F.γ := by
    calc _ = (F.β * F.γ) * (mt V x).map q.pr * (F.β * F.γ) := by rw [F.βγ, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [g, Matrix.mul_assoc]
  refine ⟨g, hg, fun a b => ?_⟩
  have h1 : (mt V x).map q.pr * F.β = F.β * g.val := by rw [hg, Matrix.mul_assoc, F.γβ, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (e a)) b
  rw [hβ] at h2
  simpa [Matrix.mul_apply, Matrix.one_apply] using h2.symm

end Loc


end GlobalTheory.FamTrace.TraceBwd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FamTrace.RedAt

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : HeightOneSpectrum (𝓞 D.host.E)} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
include hq

theorem val_lt_of_pr {y : D.host.E} (hy : valuation K (q.pr (incA D y)) < 1) : PP.valuation D.host.E y < 1 := by
  have val_lt_one_iff (x : 𝓞 D.host.E) :
      valuation K (q.pr (incA D (x : D.host.E))) < 1 ↔ x ∈ PP.asIdeal := by
    by_cases hx : x = 0
    · subst hx; simp
    have h0 : (q.pr.comp (incA D)) (x : D.host.E) ≠ 0 := (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
    rw [hq.2 x hx, ← q.sec_pr, ← q.int_iff]
    change valuation K ((q.pr.comp (incA D)) x) < 1 ↔ ¬ valuation K ((q.pr.comp (incA D)) (x : D.host.E)⁻¹) ≤ 1
    rw [map_inv₀, map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]
  have val_le_one (x : 𝓞 D.host.E) : valuation K (q.pr (incA D (x : D.host.E))) ≤ 1 := by
    have h := GlobalTheory.FinPl.SplitApprox.val_le q 1 one_pos (incA D (x : D.host.E)) (finPart D (incA D (x : D.host.E)))
      (GlobalTheory.FinPl.SplitApprox.tmul_mem (a := 1) (fun v => by rw [map_one]; exact one_mem _) x.2) (by simp)
    simpa using h
  by_cases hle : PP.valuation D.host.E y ≤ 1
  · obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hle
    have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
      le_antisymm (val_le_one _) (not_lt.1 fun h' => d.2 ((val_lt_one_iff _).1 h'))
    have hr : r ∈ PP.asIdeal := by
      refine (val_lt_one_iff r).1 ?_
      rw [show ((r : 𝓞 D.host.E) : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd,
        mul_one]
      exact hy
    have hdv : PP.valuation D.host.E ((d : 𝓞 D.host.E) : D.host.E) = 1 :=
      le_antisymm (PP.valuation_le_one _) (not_lt.1 fun h' => d.2 ((HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 h'))
    have h1 : PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).2 hr
    rw [← e, map_mul] at h1
    rwa [show algebraMap (𝓞 D.host.E) D.host.E (d : 𝓞 D.host.E) = ((d : 𝓞 D.host.E) : D.host.E) from rfl, hdv, mul_one] at h1
  · exfalso
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hle (by simp)
    have h1 : PP.valuation D.host.E y⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hle)
    have h2 := GlobalTheory.SeeSaw.LevChi.val_rat_lt q hq h1
    have h3 : q.pr (incA D y) * q.pr (incA D y⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ hy0, map_one, map_one]
    have h4 := congrArg (valuation K) h3
    rw [map_mul, map_one] at h4
    have h5 : valuation K (q.pr (incA D y)) * valuation K (q.pr (incA D y⁻¹)) < 1 :=
      (mul_le_of_le_one_right' h2.le).trans_lt hy
    exact (ne_of_lt h5) h4

theorem hasRes_of_pr {z : AE D} (c : 𝓞 D.host.E) (hz : valuation K (q.pr z - q.pr (incA D (c : D.host.E))) < 1) :
    GlobalTheory.Mem.Col2.HasRes PP (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z)) (Ideal.Quotient.mk PP.asIdeal c) := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : Valued.v (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) < 1 := by
    rw [← GlobalTheory.Mem.Col2.adAt_inclE D.host.F, ← map_sub, e, add_sub_cancel_left]
    exact valued_nat_mul_lt hr hN'
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    refine GlobalTheory.SeeSaw.LevChi.val_pr_lt q hq ?_
    have e2 : toEAf D (z - incA D y) = toEAf D z - Formalism.UG.inclE (FiniteAdeleRing (𝓞 D.host.F) D.host.F) y := by
      rw [RingHom.map_sub]
      rfl
    rw [e2, map_sub, GlobalTheory.Mem.Col2.adAt_inclE]
    exact h1
  have h3 : valuation K (q.pr (incA D (y - (c : D.host.E)))) < 1 := by
    have e3 : q.pr (incA D (y - (c : D.host.E))) = (q.pr z - q.pr (incA D (c : D.host.E))) - q.pr (z - incA D y) := by
      rw [map_sub, map_sub, map_sub]
      ring
    rw [e3]
    exact Valuation.map_sub_lt _ hz h2
  have h4 := val_lt_of_pr q hq h3
  refine ⟨c, rfl, ?_⟩
  have e4 : GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) (algebraMap (𝓞 D.host.E) D.host.E c) =
      (GlobalTheory.Mem.Col2.adAt D.host.F PP (toEAf D z) - algebraMap D.host.E (PP.adicCompletion D.host.E) y) +
        algebraMap D.host.E (PP.adicCompletion D.host.E) (y - (c : D.host.E)) := by
    rw [map_sub, sub_add_sub_cancel]
  rw [e4]
  refine Valuation.map_add_lt _ h1 ?_
  rw [valued_algebraMap]
  exact h4

end Split

end GlobalTheory.FamTrace.RedAt

namespace GlobalTheory.FamTrace.RedAt


end GlobalTheory.FamTrace.RedAt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MovesEntries

theorem map_mulVec_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) (r s : Fin n) (h1 : f (y s) = 1)
    (h0 : ∀ b, b ≠ s → y b = 0) : f ((M *ᵥ y) r) = f (M r s) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [Finset.sum_eq_single s]
  · rw [h1, mul_one]
  · intro b _ hb
    rw [h0 b hb, map_zero, mul_zero]
  · intro hs
    exact (hs (Finset.mem_univ _)).elim

theorem toEAf_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] α := by
  rfl

theorem infPart_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0 := by
  have : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e)
      = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e := rfl
  rw [this, TensorProduct.zero_tmul]

theorem coord_int (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (y : Fin S.rank → AE D) (hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True)) (i : Fin S.rank) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D (y i)) ∈ Formalism.BasicNotions.intV D.host.E v := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hxi : IsIntegral ℤ (x i) := (hL x).1 hx i
    have h1 : Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)))
        = ((x i) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))
          * ((1 : D.host.E) ⊗ₜ[D.host.F] (evalV D.host.F v α : v.adicCompletion D.host.F)) := by
      rw [toEAf_pair, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
      rfl
    show Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i))) ∈ _
    rw [h1]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x i, ⟨⟨x i, hxi⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨evalV D.host.F v α, hα v⟩, rfl⟩))
  | zero =>
    rw [Pi.zero_apply, (toEAf D).map_zero, (Formalism.UG.prV (E := D.host.E) v).map_zero]
    exact Subring.zero_mem _
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, (toEAf D).map_add, (Formalism.UG.prV (E := D.host.E) v).map_add]
    exact Subring.add_mem _ ha hb
  | neg a _ ha =>
    rw [Pi.neg_apply, (toEAf D).map_neg, (Formalism.UG.prV (E := D.host.E) v).map_neg]
    exact Subring.neg_mem _ ha

theorem finM_entry_int : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  intro D S n hn L hL κ hκ v r s
  subst hn
  let x : Fin S.rank → D.host.E := Pi.single s 1
  have hx : x ∈ L := by
    rw [hL]
    intro k
    by_cases hk : k = s
    · subst hk
      simp only [x, Pi.single_eq_same]
      exact isIntegral_one
    · simp only [x, Pi.single_eq_of_ne hk]
      exact isIntegral_zero
  let y : Fin S.rank → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 * x i)
  have hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    refine AddSubgroup.subset_closure ⟨1, ?_, fun w hw => (hw trivial).elim, 1, rfl, x, hx, rfl⟩
    intro w
    rw [map_one]
    exact one_mem _
  have hid : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := by
    intro i
    refine Submodule.mem_inf.2 ⟨infPart_pair D _ _, ?_⟩
    rw [Submodule.mem_iInf]
    intro w
    exact (w.2 trivial).elim
  have h := coord_int D S L hL v _ ((hκ y hid).1 hy) r
  have h2 : toEAf D ((Formalism.L2.Theta.mt S κ *ᵥ y) r) = toEAf D (Formalism.L2.Theta.mt S κ r s) := by
    refine map_mulVec_single (toEAf D) _ y r s ?_ ?_
    · simp only [y, x, toEAf_pair, Pi.single_eq_same, one_mul]
      rfl
    · intro b hb
      simp only [y, x, Pi.single_eq_of_ne hb, mul_zero, TensorProduct.tmul_zero]
  rw [h2] at h
  exact h

end GlobalTheory.FinPl.MovesEntries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteMatrixEntryIntegralOfKeepsStandardLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  first | exact @GlobalTheory.FinPl.MovesEntries.finM_entry_int | exact GlobalTheory.FinPl.MovesEntries.finM_entry_int | (intros; apply GlobalTheory.FinPl.MovesEntries.finM_entry_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCompactLevelProperty
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemColGroupIff
noncomputable section

namespace GlobalTheory.SeeSaw.LevMem

section Columns

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col _root_.Formalism.L2.DIV _root_.Formalism.L2.Ker Formalism.UG Formalism.UG.P _root_.Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr
  GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.LevRead GlobalTheory.Mem.Col2.TC.GLev0 Matrix
open scoped TensorProduct

section Pts

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def IsInt (m : GL (Fin n) (AfE F E)) : Prop := (∀ i j, m.1 i j ∈ RInt F E) ∧ ∀ i j, (m⁻¹).1 i j ∈ RInt F E

theorem isInt_of {m : GL (Fin n) (AfE F E)} (h : ∀ z : Fin n → AfE F E, (∀ i, z i ∈ RInt F E) ↔ ∀ i, (m.1 *ᵥ z) i ∈ RInt F E) :
    IsInt m := by
  have h1 : ∀ j i, (Pi.single j 1 : Fin n → AfE F E) i ∈ RInt F E := fun j i => by
    rw [Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨fun i j => by simpa using (h _).1 (h1 j) i, fun i j => ?_⟩
  have := (h ((m⁻¹).1 *ᵥ Pi.single j 1)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    exact h1 j) i
  simpa using this

variable [StarRing E] {hc : CMData F E} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

end Pts

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

end Columns

section LocalField

open ValuativeRel IsLocalRing Matrix GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos Reduces)

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

end LocalField

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colPos)
open GlobalTheory.SymBridge

section Adelic

variable {D : D7}

theorem mem_latHat_iff {n : ℕ} {L : Set (Fin n → D.host.E)} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D n)
    (z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) : z ∈ latHat D.host.F D.host.E L ↔ ∀ i, z i ∈ intAE D := by
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hy
      exact AddSubgroup.subset_closure ⟨a, ha, ⟨x i, (hL x).1 hx i⟩, rfl⟩
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | neg y _ hy => exact neg_mem hy
  · intro h
    rw [← Finset.univ_sum_single z]
    refine sum_mem fun i _ => ?_
    have hi := h i
    generalize z i = c at hi
    induction hi using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      refine AddSubgroup.subset_closure ⟨a, ha, Pi.single i (x : D.host.E), (hL _).2 fun j => ?_, funext fun j => ?_⟩
      · rw [Pi.single_apply]
        split_ifs
        exacts [x.isIntegral_coe, isIntegral_zero]
      · rw [Pi.single_apply, Pi.single_apply]
        split_ifs
        exacts [rfl, (TensorProduct.tmul_zero _ _).symm]
    | zero => rw [Pi.single_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [Pi.single_add]; exact add_mem hy hz
    | neg y _ hy => rw [Pi.single_neg]; exact neg_mem hy


set_option maxHeartbeats 1000000 in
theorem moves_iff {V : HSp D} {L : GlobalTheory.FinPl.Lat V} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D V.rank) {κ : GA D V} {n : ℕ} (hn : V.rank = n)
    {y : GL (Fin n) (EF D)} (hy : finM V hn κ = y.1) :
    GlobalTheory.FinPl.Moves V κ L L (fun _ => True) ↔ IsInt (F := D.host.F) (E := D.host.E) y := by
  subst hn
  have h1 : ∀ a : Fin V.rank → AE D, (∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True) →
      (a ∈ GlobalTheory.FinPl.latV V L (fun _ => True) ↔ ∀ i, toEAf D (a i) ∈ Formalism.L2.DIV.RInt D.host.F D.host.E) := fun a ha =>
    (GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ a ha).trans ((mem_latHat_iff hL _).trans
      (forall_congr' fun i => GlobalTheory.IdemSupport.mem_intAE_iff _))
  have h2 : ∀ (a : Fin V.rank → AE D) i, toEAf D ((mt V κ *ᵥ a) i) = (y.1 *ᵥ fun j => toEAf D (a j)) i := fun a i => by
    rw [← hy]
    exact RingHom.map_mulVec (toEAf D) _ a i
  constructor
  · intro h
    refine isInt_of fun z => ?_
    let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
    choose a ha ha' using fun i => GlobalTheory.KStabBridge.exists_fin_lift (D := D) (sw.symm (z i))
    have hz : ∀ i, toEAf D (a i) = z i := fun i => (congrArg sw (ha' i)).trans (sw.apply_symm_apply _)
    have hi : ∀ i, a i ∈ GlobalTheory.FinPl.idAt D fun _ => True := fun i =>
      Submodule.mem_inf.2 ⟨ha i, (Submodule.mem_iInf _).2 fun u => absurd trivial u.2⟩
    have := h a hi
    rw [h1 a hi, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ hi)] at this
    simp only [h2, hz] at this
    exact this
  · intro h a ha
    rw [h1 a ha, h1 _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ κ ha)]
    simp only [h2]
    refine ⟨PtExist.mulVec_int h.1, fun h' i => ?_⟩
    have := PtExist.mulVec_int h.2 h' i
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this

section Split

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E}

end Split

variable {u : D.what₂.Word} {a : XPart D u}

end Adelic

end GlobalTheory.SeeSaw.LevMem

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.FinPl.AwayLevel.single_natCast_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (T : ℕ) (j b : Fin n) [Decidable (b = j)] :
    (Pi.single j (T : K) : Fin n → K) b = ((if b = j then (T : 𝓞 K) else 0 : 𝓞 K) : K) := by
  by_cases hb : b = j
  · subst hb
    simp
  · simp [hb]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GluedPlaceSourceConstantProofStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluedPlaceSourceConstant_proof : ∀ D : D7, GlobalTheory.FinPl.SourceExact D := by
  first | exact @GlobalTheory.FinPl.sourceExact | exact GlobalTheory.FinPl.sourceExact | (intros; apply GlobalTheory.FinPl.sourceExact <;> assumption)
end
