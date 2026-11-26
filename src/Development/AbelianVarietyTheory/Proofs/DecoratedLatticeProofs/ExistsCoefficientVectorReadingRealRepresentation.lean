module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselUnfoldingOrbitMemParabolicMulStabiliser
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PullbackAndTensorModule

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.Top

theorem exists_pairB_of_range_eq {ι : Type} [Fintype ι] {n : ℕ} (G G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n)
    (o : Frames G') (ho : (fun τ => (o.1 τ)⁻¹) = 1) {V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Frames G → ℂ))
    (hinj : Function.Injective j) (hr : LinearMap.range j = ValC G lam) (ℓ : V →ₗ[ℂ] ℂ) :
    ∃ w ∈ Formalism.L2.DIV.VV ℂ lam, ∀ v, ℓ v = Formalism.L2.DIV.pairB lam (Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)) w := by
  have key : ∀ P, Formalism.L2.Col.polOf G' (shiftOf lam) o (fnOf G (shiftOf lam) 1 P) = P := by
    intro P
    have h := Formalism.L2.Col.polOf_fnOf G' (shiftOf lam) o P
    rw [ho] at h
    exact h
  have hval : ∀ v, ∃ P ∈ Formalism.L2.DIV.VV ℂ lam, j v = fnOf G (shiftOf lam) 1 P := by
    intro v
    have hv : j v ∈ ValC G lam := hr ▸ LinearMap.mem_range_self j v
    obtain ⟨P, hP, hPv⟩ := Submodule.mem_map.mp hv
    rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV] at hP
    exact ⟨P, hP, hPv.symm⟩
  let φ : V →ₗ[ℂ] Formalism.L2.DIV.Pol ℂ ι n :=
    { toFun := fun v => Formalism.L2.Col.polOf G' (shiftOf lam) o (j v)
      map_add' := fun x y => by rw [map_add (f := _)]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_add (j x) (j y)
      map_smul' := fun c x => by rw [map_smul]; exact (Formalism.L2.Col.polOf G' (shiftOf lam) o).map_smul c (j x) }
  have hφ : ∀ v, φ v = Formalism.L2.Col.polOf G' (shiftOf lam) o (j v) := fun _ => rfl
  have hmem : ∀ v, φ v ∈ Formalism.L2.DIV.VV ℂ lam := by
    intro v
    obtain ⟨P, hP, e⟩ := hval v
    rw [hφ, e, key]
    exact hP
  let φ' : V →ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam := φ.codRestrict _ hmem
  have hφ' : ∀ v, (φ' v : Formalism.L2.DIV.Pol ℂ ι n) = φ v := fun _ => rfl
  have inj : Function.Injective φ' := by
    intro v v' h
    have h' : φ v = φ v' := by rw [← hφ', ← hφ', h]
    obtain ⟨P, -, e⟩ := hval v
    obtain ⟨P', -, e'⟩ := hval v'
    rw [hφ, hφ, e, e', key, key] at h'
    apply hinj
    rw [e, e', h']
  have surj : Function.Surjective φ' := by
    intro x
    have hx : fnOf G (shiftOf lam) 1 x.1 ∈ LinearMap.range j := by
      rw [hr]
      refine Submodule.mem_map.mpr ⟨x.1, ?_, rfl⟩
      rw [GlobalTheory.Pdv.FormsStd.cSpan_eq_VV]
      exact x.2
    obtain ⟨v, hv⟩ := hx
    refine ⟨v, Subtype.ext ?_⟩
    rw [hφ', hφ, hv, key]
  let e := LinearEquiv.ofBijective φ' ⟨inj, surj⟩
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam) := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam)
  let ψ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam) := ℓ ∘ₗ e.symm.toLinearMap
  have hB : (pairBK (K := ℂ) lam).flip.Nondegenerate := by
    have := pairingBNondegenerate_holds ℂ ι n lam
    exact LinearMap.flip_nondegenerate.mpr this
  let w := (LinearMap.BilinForm.toDual _ hB).symm ψ
  have hw : ∀ x, ψ x = pairBK lam x w := by
    intro x
    have h1 : LinearMap.BilinForm.toDual _ hB w = ψ := LinearEquiv.apply_symm_apply _ _
    rw [← h1, LinearMap.BilinForm.toDual_def, LinearMap.flip_apply]
  refine ⟨w.1, w.2, fun v => ?_⟩
  have h2 : ℓ v = ψ (e v) := by simp [ψ]
  rw [h2, hw, pairBK_apply]
  rfl

end GlobalTheory.Core.Rk.Top

namespace GlobalTheory.Core.Rk.Top

theorem sgT_eq_perIn_sgT {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = (I.perIn u a).sgT := by
  funext τ
  unfold Formalism.L2.Forms.sgT PerIn.sgT Formalism.L2.Forms.shW GlobalTheory.Mem.Col2.shW
  congr 1
  funext i
  have h1 : (((I.rec7 l Z).fm u).sg τ).w i = ((I.perIn u a).sg τ).w i := rfl
  have h2 : (I.rec7 l Z).R = B.R := rfl
  rw [h1, h2]
  have hd : 2 ∣ B.R.t + 1 := by
    obtain ⟨k, hk⟩ := B.R.t_odd
    exact ⟨k + 1, by omega⟩
  rw [Nat.mul_div_assoc _ hd]
  push_cast
  ring

theorem exists_pairB_of_isJ : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  intro B X I l Z u a S MX j hJ ℓ
  have hr := hJ.range
  rw [sgT_eq_perIn_sgT I l Z u a] at hr
  have e : (fun τ => ((GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  exact exists_pairB_of_range_eq _ _ _ _ e j hJ.inj hr ℓ

end GlobalTheory.Core.Rk.Top

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coefficientVector_reading_realRepresentation_form : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) {S : (I.rec7 l Z).what₂.Tau → SPar} (MX : DSModel (I.rec7 l Z).sp.X' S) (j : SmT MX →ₗ[ℂ] (Formalism.L2.Forms.FrP (I.rec7 l Z) → ℂ)), GlobalTheory.Core.Rk.Top.IsJ u MX j → ∀ ℓ : SmT MX →ₗ[ℂ] ℂ, ∃ w ∈ Formalism.L2.DIV.VV ℂ (I.perIn u a).sgT, ∀ v, ℓ v = Formalism.L2.DIV.pairB (I.perIn u a).sgT (Formalism.L2.Col.polOf (GlobalTheory.Mem.Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m - 1)) (Formalism.L2.Forms.shiftOf (I.perIn u a).sgT) (GlobalTheory.Mem.Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m - 1)) (j v)) w := by
  first | exact @GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | exact GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ | (intros; apply GlobalTheory.Core.Rk.Top.exists_pairB_of_isJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLatt
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLatt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocMod.StMoves

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_mul {m n p : Type} [Fintype n] {A : Matrix m n k} {B : Matrix n p k} (hA : ∀ i j, A i j ∈ 𝒪[k])
    (hB : ∀ i j, B i j ∈ 𝒪[k]) : ∀ i j, (A * B) i j ∈ 𝒪[k] := fun i j =>
  Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hA i l) (hB l j)

theorem int_one_sub {m a b : Type} [DecidableEq m] (f : a → m) (g' : b → m) :
    ∀ i j, ((1 : Matrix m m k).submatrix f g') i j ∈ 𝒪[k] := fun i j => by
  change (1 : Matrix m m k) (f i) (g' j) ∈ 𝒪[k]
  rw [Matrix.one_apply]
  split_ifs
  exacts [Subring.one_mem _, Subring.zero_mem _]

theorem mt_mul (S : HSp D) (a b : GA D S) : mt S (a * b) = mt S a * mt S b := by simp [Formalism.L2.Theta.mt]

theorem alg_frame {n : ℕ} {Y R A' : Type} [Fintype Y] [DecidableEq Y] [CommRing R] [CommRing A'] (pr : R →+* k) (toE : R →+* A')
    (π : A' →+* k) (hmap : ∀ x, π (toE x) = pr x) (mg mt' mh b : Matrix (Fin n) (Fin n) R) (βv I : Matrix (Fin n) (Fin n) A')
    (Fβ : Matrix (Fin n) Y k) (Fγ : Matrix Y (Fin n) k) (e : Y ≃ Fin n) (hγβ : Fγ * Fβ = 1) (hb : b.map toE = βv)
    (hmv : (mt' * b).map pr = Fβ.submatrix id e.symm) (hg1 : mg * mt' = mt' * mh) (hfin : mh.map toE * βv = βv * I) :
    Fγ * mg.map pr * Fβ = (1 : Matrix Y Y k).submatrix id e.symm * I.map π * (1 : Matrix Y Y k).submatrix e.symm id := by
  have hm : ∀ N : Matrix (Fin n) (Fin n) R, (N.map toE).map π = N.map pr := fun N => Matrix.ext fun _ _ => hmap _
  have eq2 : mg.map pr * Fβ.submatrix id e.symm = Fβ.submatrix id e.symm * I.map π := by
    rw [← hmv, ← Matrix.map_mul, ← Matrix.mul_assoc, hg1, Matrix.mul_assoc, Matrix.map_mul, ← hm (mh * b), Matrix.map_mul,
      hb, hfin, Matrix.map_mul, ← hb, hm, ← Matrix.mul_assoc, ← Matrix.map_mul]
  have eq1 : Fβ = Fβ.submatrix id e.symm * (1 : Matrix Y Y k).submatrix e.symm id := by
    rw [Matrix.submatrix_mul_equiv, Matrix.mul_one]; rfl
  have eq3 : Fγ * Fβ.submatrix id e.symm = (1 : Matrix Y Y k).submatrix id e.symm := by
    rw [← hγβ]
    exact Matrix.submatrix_mul_equiv Fγ Fβ id (Equiv.refl _) e.symm
  conv_lhs => rw [eq1]
  rw [Matrix.mul_assoc Fγ, ← Matrix.mul_assoc _ (Fβ.submatrix id e.symm), eq2, ← eq3]
  simp only [Matrix.mul_assoc]

theorem int_of_mem_St (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (hq : Formalism.L2.NTheta.IsIdemAt q.e PP)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y)
    (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank)
    (hM : GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm))
    (g : GA D S) (hg : Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β) :
    ∀ i j, (F.γ * (mt S g).map q.pr * F.β) i j ∈ 𝒪[k] := by
  obtain ⟨Y0, hY0⟩ := hg
  obtain ⟨π, h1, -, h3, -⟩ := GlobalTheory.LocMod.LevBack.exists_chart q hq
  have hb' : (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map (toEAf D) = β.val :=
    Matrix.ext fun _ _ => GlobalTheory.LocMod.LevBack.toEAf_finEmb _
  have hmv : (mt S t * β.val.map (GlobalTheory.AdelicLatMove.finEmb D)).map q.pr = F.β.submatrix id e.symm := hM _ hb'
  have hZi : ∀ i j, ((Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val.map π) i j ∈ 𝒪[k] := fun i j => h3 (Y0.val i j)
  have hmap : ∀ N : Matrix (Fin S.rank) (Fin S.rank) (AE D), (N.map (toEAf D)).map π = N.map q.pr :=
    fun N => Matrix.ext fun _ _ => h1 _
  have hfin : Lev.finE S (t⁻¹ * g * t) * β = β * Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0 := by
    rw [← hY0]
    simp [Formalism.L2.DIV.frGL]
  have hfin' : (mt S (t⁻¹ * g * t)).map (toEAf D) * β.val = β.val * (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val := by
    have := congrArg Units.val hfin
    rwa [Units.val_mul, Units.val_mul] at this
  have hg1 : mt S g * mt S t = mt S t * mt S (t⁻¹ * g * t) := by
    rw [← mt_mul, ← mt_mul]; congr 1; group
  rw [alg_frame q.pr (toEAf D) π h1 (mt S g) (mt S t) (mt S (t⁻¹ * g * t)) (β.val.map (GlobalTheory.AdelicLatMove.finEmb D)) β.val
    (Formalism.L2.DIV.intGL D.host.F D.host.E S.rank Y0).val F.β F.γ e F.γβ hb' hmv hg1 hfin']
  exact int_mul (int_mul (int_one_sub _ _) hZi) (int_one_sub _ _)


open scoped Pointwise in
theorem moves_of_mem_St : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  intro D k _ _ _ _ q PP hq S L hL Y _ _ F hF t β e hM g hg
  obtain ⟨gl, h1, h2⟩ := GlobalTheory.GlEmbed.exists_gl D k q S Y F.β F.γ F.βγ F.γβ
  have hlat : (⟨F.β, F.γ, F.βγ, F.γβ, gl, h1, h2⟩ : GlobalTheory.FinPl.Frame q S Y).IsLat L (GlobalTheory.StepData.latOf 1) := fun x => by
    rw [GlobalTheory.StepData.mem_latOf_one]; exact hF x
  refine (GlobalTheory.T.stabilizes_selfDual_iff_frame_matrix_stabilizes D k q S Y _ L _ hL hlat g).2 ?_
  have hA : ∀ i j, (GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g).val i j ∈ 𝒪[k] :=
    int_of_mem_St q hq S F t β e hM g hg
  have hAi : ∀ i j, ((GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g)⁻¹).val i j ∈ 𝒪[k] := by
    rw [← map_inv]
    refine int_of_mem_St q hq S F t β e hM g⁻¹ ?_
    have : t⁻¹ * g⁻¹ * t = (t⁻¹ * g * t)⁻¹ := by group
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hg
  have hK : GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g ∈ GlobalTheory.StepData.stabLat 1 := by
    rw [GlobalTheory.StepData.mem_stabLat, inv_one, one_mul, mul_one]
    exact GlobalTheory.StepData.mem_KO.2 ⟨hA, hAi⟩
  have hs := GlobalTheory.StepData.mem_stabLat_iff.1 hK
  set A := GlobalTheory.SeeSaw.coordHom S q.pr F.β F.γ F.βγ F.γβ g
  ext y
  conv_rhs => rw [← hs]
  change (∃ x, x ∈ GlobalTheory.StepData.latOf 1 ∧ A • x = y) ↔ _
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (GlobalTheory.StepData.mulVec_mem_latOf A).2 hx
  · intro hy
    refine ⟨A⁻¹ • y, (GlobalTheory.StepData.mulVec_mem_latOf A).1 ?_, smul_inv_smul _ _⟩
    have : A.val *ᵥ (A⁻¹ • y) = y := smul_inv_smul A y
    rwa [this]

end GlobalTheory.LocMod.StMoves
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjugateStabilizerKeepsMovedFrameLattStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_conjugate_stabilizer_keeps_movedFrameLattice : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E}, Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (S : HSp D) (L : GlobalTheory.FinPl.Lat S), IsSelfDualC S L → ∀ {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y), (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)) → ∀ (t : GA D S) (β : GL (Fin S.rank) (Lev.EAf D)) (e : Y ≃ Fin S.rank), GlobalTheory.LocMod.MovedTo (GlobalTheory.LocMod.ofSplit q) S t β (F.β.submatrix id e.symm) → ∀ g : GA D S, Lev.finE S (t⁻¹ * g * t) ∈ Formalism.L2.DIV.St β → GlobalTheory.FinPl.Moves S g L L (· = q.v) := by
  first | exact @GlobalTheory.LocMod.StMoves.moves_of_mem_St | exact GlobalTheory.LocMod.StMoves.moves_of_mem_St | (intros; apply GlobalTheory.LocMod.StMoves.moves_of_mem_St <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

namespace GlobalTheory.Core.Mi.LatMatch.TraceX

theorem mulVec_mem_ideal {R : Type} [CommRing R] {I : Ideal R} {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) {y : Fin n → R}
    (hy : ∀ i, y i ∈ I) (k : Fin m) : (A *ᵥ y) k ∈ I := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (hy i)

theorem latV_iff_hatL {D : D7} (S : HSp D) (L : Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) (y : Fin S.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D P) :
    y ∈ latV S L P ↔ (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L :=
  ⟨GlobalTheory.LatVHat.latV_mem_hatL D S L P y, GlobalTheory.HatLatV.mem_latV_of_hatL D S L P y hy⟩

theorem hat_reindex {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (hn : m = n)
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin m → E ⊗[F] Formalism.L2.Herm.Af F) :
    z ∈ Formalism.L2.Herm.hatL (F := F) (L.map ((LinearEquiv.funCongrLeft E E (finCongr hn)).toLinearMap.restrictScalars (𝓞 E))) ↔
      (fun j => z (Fin.cast hn.symm j)) ∈ Formalism.L2.Herm.hatL (F := F) L := by
  subst hn
  have e : L.map ((LinearEquiv.funCongrLeft E E (finCongr (rfl : m = m))).toLinearMap.restrictScalars (𝓞 E)) = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [e]
  rfl

theorem transport (D : D7) (I : AutInst) (ιE : I.E ≃+* D.host.E) (hId : ∀ y, HEq (ιE y) y)
    (hI : I = Formalism.L2.SG.InstExistsPf.instOf D) (hr : (D.sp.Y 0).rank = I.n)
    (ιA : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F ≃+* D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)
    (hrat : ∀ x : I.E, ιA (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) =
      Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (ιE x))
    (hint : ∀ a, a ∈ IntAf I.F I.E ↔ ιA a ∈ IntAf D.host.F D.host.E)
    {n : ℕ} (q : Fin n → Fin I.n → I.E) (c : Fin n → GlobalTheory.AdForm.EF D) :
    (∑ i, ιA.symm (c i) • incl I (q i)) ∈ I.Lf ↔
      (∑ i, c i • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) (ιE (q i (Fin.cast hr k)))) ∈
        Formalism.L2.Herm.hatL (F := D.host.F) (latS D) := by
  subst hI
  have hid : ∀ y, ιE y = y := fun y => eq_of_heq (hId y)
  have hA : ∀ a, ιA a = a := GlobalTheory.Core.Mi.FinFrame.eq_self_of_rat_of_int (Formalism.L2.SG.InstExistsPf.instOf D).F
    (Formalism.L2.SG.InstExistsPf.instOf D).E ιA.toRingHom
    (fun x => (hrat x).trans (congrArg _ (hid x))) (fun a ha => (hint a).1 ha)
  have hA' : ∀ a, ιA.symm a = a := fun a => (hA _).symm.trans (ιA.apply_symm_apply a)
  simp only [hid, hA']
  have e : latS D = GlobalTheory.PlaceModel.latFrame (Yc D 0) := GlobalTheory.ConjPlaceRed.crdLat_eq_latFrame (D.sp.Y 0)
  rw [e]
  exact (GlobalTheory.ConjPlaceRed.mem_Lf D _).symm

theorem fin_emb {D : D7} {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (w : Fin A.rank → AE D) :
    (fun k => toEAf D ((d.j0 *ᵥ (o.jA *ᵥ w)) k)) =
      ∑ i, toEAf D (w i) • fun k => Formalism.UG.inclE (F := D.host.F) (Formalism.MainNotions.S.Af D.host.F) ((d.i₀ * o.iA) k i) := by
  have h2 : HMul.hMul d.j0 o.jA = (d.i₀ * o.iA).map (incA D) := (Matrix.map_mul (f := incA D)).symm
  rw [Matrix.mulVec_mulVec, h2]
  funext k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    GlobalTheory.Core.Mi.FinFrame.toEAf_incA]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem fin_mt {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (y : Fin V.rank → AE D) :
    GlobalTheory.AdForm.finM V hn g *ᵥ (fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D ((Formalism.L2.Theta.mt V g *ᵥ y) (Fin.cast hn.symm j)) := by
  subst hn
  funext i
  exact (RingHom.map_mulVec (toEAf D) (Formalism.L2.Theta.mt V g) y i).symm


set_option maxHeartbeats 1600000 in
theorem trace_iff : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  intro D X h u ψ F tr hK B a₀ hId hL hAd h0 v y hy
  have hn := Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)
  have hy' : ∀ k, (B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k ∈ idAt D (· = v) :=
    mulVec_mem_ideal _ (mulVec_mem_ideal _ (mulVec_mem_ideal _ hy))
  refine (latV_iff_hatL _ _ _ _ hy).trans
    (Iff.trans ?_ (latV_iff_hatL _ _ _ _ hy').symm)
  change (fun i => toEAf D (y i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (lat0 F) ↔
    (fun k => toEAf D ((B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y))) k)) ∈
      Formalism.L2.Herm.hatL (F := D.host.F) (latS D)
  refine (hat_reindex hn F.cls0.lev.Lb _).trans ?_
  have H := hL.1 (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j)))
  have e1 : (tr.h0⁻¹).1.1 *ᵥ (tr.h0.1.1 *ᵥ fun j => toEAf D (y (Fin.cast hn.symm j))) =
      fun j => toEAf D (y (Fin.cast hn.symm j)) := by
    rw [Matrix.mulVec_mulVec]
    have : HMul.hMul (tr.h0⁻¹).1.1 tr.h0.1.1 = 1 := Units.inv_mul tr.h0.1
    rw [this, Matrix.one_mulVec]
  rw [e1] at H
  refine H.trans ?_
  rw [← h0.2, fin_mt, fin_emb]
  refine (transport D X.B.I X.ιE hId h (rank_eq X h) tr.ιA tr.ιA_rat tr.ιA_int
    (fun i => X.crd (Formalism.L2.SG.ColDict.qFr tr.wt i)) _).trans ?_
  simp only [hAd _ _]
  refine iff_of_eq (congrArg (· ∈ Formalism.L2.Herm.hatL (F := D.host.F) (latS D)) ?_)
  exact (Fintype.sum_equiv (finCongr hn) _ _ fun i => rfl).symm

end GlobalTheory.Core.Mi.LatMatch.TraceX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportCorrectionCarriesColumnLatticeRowTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportCorrection_carries_columnLattice_rowTrace : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (hK : X.LevelSubgroupCharacter) (B : SBes X h u ψ (D.sp.X 0)) (a₀ : GA D (D.sp.X 0)), GlobalTheory.Core.Mi.IdE X → Formalism.L2.SG.ColDict.LevelMatch X tr hK → B.Adapted tr.wt → IsTransportAdelicCorrection tr a₀ → ∀ (v : GlobalTheory.FinPl.Pl D) (y : Fin (D.sp.X 0).rank → AE D), (∀ i, y i ∈ idAt D (· = v)) → (y ∈ latV (D.sp.X 0) (lat0 F) (· = v) ↔ B.d.j0 *ᵥ (B.o.jA *ᵥ (Formalism.L2.Theta.mt (D.sp.X 0) a₀ *ᵥ y)) ∈ latV (D.sp.Y 0) (latS D) (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | exact GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff | (intros; apply GlobalTheory.Core.Mi.LatMatch.TraceX.trace_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocAgree

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem latV_congr (S : HSp D) (L : Lat S) {P P' : Pl D → Prop} (h : ∀ w, P w ↔ P' w) :
    latV S L P = latV S L P' :=
  le_antisymm (latV_mono S L fun w => (h w).1) (latV_mono S L fun w => (h w).2)

theorem latV_le_of_int_smul_on (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (R : Pl D → Prop) (hR : ∀ v, R v → ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L R ≤ latV S M R := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : R w
    · have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
        have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)
        have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
        have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
          map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
        exact h2.trans (h4 ▸ h1)
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

theorem latV_le_finite (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) (T : Finset (Pl D)) :
    latV S L (fun p => P p ∧ p ∈ T) ≤ latV S N (fun p => P p ∧ p ∈ T) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact latV_le_of_int_smul_on S L N d hd hLN _ fun v hv => absurd hv.2 (Finset.notMem_empty v)
  | insert a T' ha ih =>
    intro z hz
    have hs := GlobalTheory.FinPlLoc.latV_idAt hz
    obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L _ {a} hs).1 hz
    rw [mem_latV_iff_parts S N _ {a} hs]
    constructor
    · by_cases hPa : P a
      · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∈ ({a} : Finset (Pl D))) ↔ w = a := by
          intro w
          simp only [Finset.mem_insert, Finset.mem_singleton]
          constructor
          · exact fun h => h.2
          · rintro rfl; exact ⟨⟨hPa, Or.inl rfl⟩, rfl⟩
        rw [latV_congr S L hiff, hP a hPa] at h1
        rw [latV_congr S N hiff]
        exact h1
      · refine latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h1
        exact absurd (Finset.mem_singleton.1 hv.2 ▸ hv.1.1) hPa
    · have hiff : ∀ w, ((P w ∧ w ∈ insert a T') ∧ w ∉ ({a} : Finset (Pl D))) ↔ (P w ∧ w ∈ T') := by
        intro w
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hw, h | h⟩, hne⟩
          · exact absurd h hne
          · exact ⟨hw, h⟩
        · rintro ⟨hw, h⟩
          exact ⟨⟨hw, Or.inr h⟩, fun e => ha (e ▸ h)⟩
      rw [latV_congr S L hiff] at h2
      rw [latV_congr S N hiff]
      exact ih h2

theorem latV_le_of_local (S : HSp D) (L N : Lat S) (d : ℤ) (hd : d ≠ 0) (hLN : ∀ x ∈ L, d • x ∈ N)
    (P : Pl D → Prop) (hP : ∀ w, P w → latV S L (· = w) = latV S N (· = w)) : latV S L P ≤ latV S N P := by
  classical
  set T := (finite_places_int (D := D) d hd).toFinset
  intro y hy
  have hs := GlobalTheory.FinPlLoc.latV_idAt hy
  obtain ⟨h1, h2⟩ := (mem_latV_iff_parts S L P T hs).1 hy
  rw [mem_latV_iff_parts S N P T hs]
  refine ⟨latV_le_finite S L N d hd hLN P hP T h1, latV_le_of_int_smul_on S L N d hd hLN _ (fun v hv => ?_) h2⟩
  intro hmem
  exact hv.2 ((Set.Finite.mem_toFinset _).2 hmem)

theorem latV_eq_of_local : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop),
    Submodule.IsFullLattice D.host.E L → Submodule.IsFullLattice D.host.E N →
    (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) →
    GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  obtain ⟨d₁, hd₁, h₁⟩ := exists_int_smul_le L N hL.fg hN.span_eq_top
  obtain ⟨d₂, hd₂, h₂⟩ := exists_int_smul_le N L hN.fg hL.span_eq_top
  exact le_antisymm (latV_le_of_local S L N d₁ hd₁ h₁ P hP)
    (latV_le_of_local S N L d₂ hd₂ h₂ P fun w hw => (hP w hw).symm)

end GlobalTheory.FinPl.LocAgree

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeCompletionEqOfLocalAgreementStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeCompletion_eq_of_local_agreement : ∀ {D : D7} (S : HSp D) (L N : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop), Submodule.IsLattice D.host.E L → Submodule.IsLattice D.host.E N → (∀ w, P w → GlobalTheory.FinPl.latV S L (· = w) = GlobalTheory.FinPl.latV S N (· = w)) → GlobalTheory.FinPl.latV S L P = GlobalTheory.FinPl.latV S N P := by
  intro D S L N P hL hN hP
  ext y
  rw [GlobalTheory.FinPlLoc.part_lat P S L y hL,
    GlobalTheory.FinPlLoc.part_lat P S N y hN]
  constructor <;> rintro ⟨hs, hl⟩ <;> refine ⟨hs, fun v hv e he => ?_⟩
  · rw [← hP v hv]
    exact hl v hv e he
  · rw [hP v hv]
    exact hl v hv e he
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAComp
open GlobalTheory.AdForm.HalfPairing

theorem conjP_not_mem {D : D7} {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e SS)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS) : Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  intro hc
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨⟨es, hes, rfl⟩, horth⟩ := he
  rw [GlobalTheory.OffIdemDen.conjP_eq_cP] at hc
  have hd : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ P (es P) := fun P hP =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes P hP)
  have hdc : ∀ P ∈ SS, GlobalTheory.IdemSupport.IsDelta Φ (GlobalTheory.IdemSupport.cP P) (cA D (es P)) := fun P hP =>
    GlobalTheory.IdemSupport.delta_conj hΦ (hd P hP)
  have h1 : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hE : Φ (∑ P ∈ SS, es P) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (es P') (GlobalTheory.IdemSupport.cP P) :=
      map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hE, Finset.sum_eq_single (GlobalTheory.IdemSupport.cP P) (fun P' hP' hne => (hd P' hP').2.2 _ (fun h => hne h.symm))
      (fun h => absurd hc h), (hd _ hc).2.1]
  have h2 : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = 1 := by
    have hC : Φ (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P) = ∑ P' ∈ SS, Φ (cA D (es P')) (GlobalTheory.IdemSupport.cP P) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact map_sum (GlobalTheory.OffIdemDen.evQ Φ (GlobalTheory.IdemSupport.cP P)) _ _
    rw [hC, Finset.sum_eq_single P (fun P' hP' hne => (hdc P' hP').2.2 _ (fun h => hne (by
        have := congrArg GlobalTheory.IdemSupport.cP h
        rwa [GlobalTheory.OffIdemDen.cP_cP, GlobalTheory.OffIdemDen.cP_cP, eq_comm] at this)))
      (fun h => absurd hP h), (hdc P hP).2.1]
  have h3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ P ∈ SS, es P) (cA D (∑ P ∈ SS, es P)) (GlobalTheory.IdemSupport.cP P)
  rw [horth, h1, h2, one_mul, GlobalTheory.IdemSupport.ev_zero] at h3
  exact one_ne_zero h3.symm

theorem halfA_smul_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E)) :
    (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have key : ∀ k : ℕ, (c : E) = (c : E) ^ k * ((c : E) ^ (-expS SS Q))⁻¹ →
      (c : E) • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := fun k hk => by
    have := nsmul_mem h (c ^ k)
    rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, Nat.cast_pow, ← hk] at this
  unfold expS at key
  split_ifs at key
  · exact key 0 (by rw [_root_.zpow_neg, zpow_one, inv_inv, pow_zero, one_mul])
  · exact key 2 (by rw [neg_neg, zpow_one, pow_two, mul_assoc, mul_inv_cancel₀ hc', mul_one])
  · exact key 1 (by rw [neg_zero, zpow_zero, inv_one, pow_one, mul_one])

theorem halfA_mem_locP_conj {D : D7} {a b : ℕ} {SS : Finset (HeightOneSpectrum (𝓞 D.host.E))}
    {M : Submodule (𝓞 D.host.E) (Formalism.L2.Col.HomE D.host.E a b)} {c : ℕ} (hc : 0 < c)
    {x : Formalism.L2.Col.HomE D.host.E a b} (hx : x ∈ halfAO SS M c) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ SS)
    (hP' : Formalism.L2.Col.conjPrime₂ P ∉ SS) : x ∈ Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := by
  have h : ((c : D.host.E) ^ (-expS SS (Formalism.L2.Col.conjPrime₂ P)))⁻¹ • x ∈
      Formalism.HermitianLatticesTheory.localization₂ (Formalism.L2.Col.conjPrime₂ P).asIdeal M := (Submodule.mem_iInf _).1 hx _
  have hcc : Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ P) = P := by
    rw [GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.conjP_eq_cP, GlobalTheory.OffIdemDen.cP_cP]
  have he : expS SS (Formalism.L2.Col.conjPrime₂ P) = -1 := by
    unfold expS; rw [if_neg hP', if_pos (by rw [hcc]; exact hP)]
  have hc' : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, neg_neg, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this

theorem halfA_mem_locP_off {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ}
    {x : Formalism.L2.Col.HomE E a b} (hx : x ∈ halfAO SS M c) (Q : HeightOneSpectrum (𝓞 E))
    (hQ : ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS)) : x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := by
  have h : ((c : E) ^ (-expS SS Q))⁻¹ • x ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal M := (Submodule.mem_iInf _).1 hx Q
  have he : expS SS Q = 0 := by
    unfold expS; rw [if_neg (fun h => hQ (Or.inl h)), if_neg (fun h => hQ (Or.inr h))]
  rwa [he, neg_zero, zpow_zero, inv_one, one_smul] at h


set_option maxHeartbeats 1000000 in
theorem zmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc _ x' hx
  have hA : ((LinearMap.toMatrix' x').map fun r => cA D e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    have hE' := hE
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE'
    have e1 : ((LinearMap.toMatrix' x').map fun r => cA D (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => cA D (es PP) * incA D r : WO S T) := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Matrix.map_apply, Matrix.sum_apply, map_sum, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => conj_comp_mem hP.cc hN (hes PP hPP) ?_
      (halfA_mem_locP_conj hc hx hPP (conjP_not_mem hE hPP))
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => halfA_smul_mem_locP hc hx Q
  obtain ⟨d, hd0, hdx, hdG⟩ := GlobalTheory.T.exists_denominator_avoiding_given_primes D.host.E _ _ _ (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx
    (fun Q hQ => halfA_mem_locP_off hx Q hQ)
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := GlobalTheory.T.offIdempotent_mem_ideal_two_integers D e SS hE c hc d hd0 hdG
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, i1, hinf, hinfc,
      mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_one] at ho'
    simp only [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_mul, f1, hs]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfAComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfAComponentsMemCompletedLatticeOffPrimesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfAComp.zmem | exact GlobalTheory.HalfAComp.zmem | (intros; apply GlobalTheory.HalfAComp.zmem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem GlobalTheory.RatHalfDense.tmul_split {F E A : Type} [Field F] [CommRing E] [Algebra F E] [CommRing A] [Algebra F A]
    (a : E) (α ι : A) (u : F) (N d : ℕ)
    (h : α = ((N * d : ℕ) : F) • algebraMap F A u + ((N * d : ℕ) : F) • ι) :
    a ⊗ₜ[F] α = (algebraMap F E (((N * d : ℕ) : F) * u) * a) ⊗ₜ[F] (1 : A) + N • (((d : E) * a) ⊗ₜ[F] ι) := by
  rw [h, TensorProduct.tmul_add]
  congr 1
  · rw [Algebra.algebraMap_eq_smul_one (A := A) u, smul_smul, ← Algebra.smul_def, TensorProduct.smul_tmul]
  · have hd' : (d : E) * a = (d : F) • a := by rw [Algebra.smul_def, map_natCast]
    rw [TensorProduct.tmul_smul, hd', ← TensorProduct.smul_tmul', ← Nat.cast_smul_eq_nsmul F, smul_smul, Nat.cast_mul]

namespace GlobalTheory.RatHalfDense

variable {D : D7}

theorem coe_stdLat (n : ℕ) :
    ((Formalism.L2.Pj.stdLat D.host.E n : Submodule _ _) : Set (Fin n → D.host.E)) = intVec D n := by
  ext x
  simp only [SetLike.mem_coe, GlobalTheory.LocM.Unim.mem_stdLat, intVec, Set.mem_setOf_eq]
  constructor
  · intro h k
    obtain ⟨c, hc⟩ := h k
    rw [← hc]
    exact c.isIntegral_coe
  · intro h k
    exact ⟨⟨x k, h k⟩, rfl⟩

theorem exists_nsmul_mem_stdHom (S T : HSp D) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO S T, t.map (infPart D) = 0 →
    (∀ i j, toEAf D (t i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) → K • t ∈ stdHom S T := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO (S := S) (T := T)
    (GlobalTheory.LocM.Unim.isLattice_stdLat S.rank) (GlobalTheory.LocM.Unim.isLattice_stdLat T.rank)
  refine ⟨K, hK, fun t h1 h2 => ?_⟩
  have := h t h1 h2
  rw [coe_stdLat, coe_stdLat] at this
  exact this

theorem mul_eq_zero_of_parts {e z : AE D} (he : infPart D e = 0) (hz : finPart D z = 0) : e * z = 0 := by
  rw [Formalism.IndefR.Eqv.infPart_eq_zero_iff_smul] at he
  rw [Formalism.IndefR.Eqv.finPart_eq_zero_iff_smul] at hz
  rw [← he, ← hz, smul_mul_smul_comm]
  have : Formalism.IndefR.Eqv.eFin D * Formalism.IndefR.Eqv.eInf D = 0 := by
    simp only [Formalism.IndefR.Eqv.eFin, Formalism.IndefR.Eqv.eInf, pairA]
    exact Prod.ext (show (0 : Ainf D.host.F) * 1 = 0 from zero_mul _) (show (1 : Af D.host.F) * 0 = 0 from mul_zero _)
  rw [this, zero_smul]

theorem exists_nat_mul_isIntegral (z : D.host.E) : ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : D.host.E) * z) := by
  have hz : IsAlgebraic ℤ z := (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, h⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at h
  rw [← Int.cast_natCast]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', Int.cast_neg, neg_mul]; exact h.neg

theorem exists_rat_add_nsmul (z : EAf D) (N : ℕ) (hN : 0 < N) :
    ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, z = eToEAf D γ + N • w := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, zero_mem _, by simp⟩
  | tmul a α =>
    obtain ⟨d, hd, hda⟩ := exists_nat_mul_isIntegral a
    have hc : ((N * d : ℕ) : D.host.F) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.mul_pos hN hd).ne'
    obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.AdeleIntA.exists_approx_adele
      (R := NumberField.RingOfIntegers D.host.F) (K := D.host.F) (((N * d : ℕ) : D.host.F)⁻¹ • α)
    have hα : α = ((N * d : ℕ) : D.host.F) • algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u
        + ((N * d : ℕ) : D.host.F) • (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hc, one_smul, add_sub_cancel]
    refine ⟨algebraMap D.host.F D.host.E (((N * d : ℕ) : D.host.F) * u) * a,
      ((d : D.host.E) * a) ⊗ₜ (((N * d : ℕ) : D.host.F)⁻¹ • α - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u), ?_, ?_⟩
    · have h1 : ((d : D.host.E) * a) ⊗ₜ[D.host.F] (1 : Formalism.L2.Herm.Af D.host.F) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inl ⟨⟨(d : D.host.E) * a, ⟨⟨(d : D.host.E) * a, hda⟩, rfl⟩⟩, rfl⟩)
      have h2 : (1 : D.host.E) ⊗ₜ[D.host.F] (((N * d : ℕ) : D.host.F)⁻¹ • α
          - algebraMap D.host.F (Formalism.L2.Herm.Af D.host.F) u) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
        Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩)
      have := mul_mem h1 h2
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    · exact tmul_split a α _ u N d hα
  | add x y hx hy =>
    obtain ⟨γ₁, w₁, hw₁, h₁⟩ := hx
    obtain ⟨γ₂, w₂, hw₂, h₂⟩ := hy
    refine ⟨γ₁ + γ₂, w₁ + w₂, add_mem hw₁ hw₂, ?_⟩
    rw [h₁, h₂, map_add (f := _), smul_add]
    abel

theorem exists_half_approx {S T : HSp D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} {E₂ : AE D} (hE : IsIdemSum E₂ Q)
    (K : ℕ) (hK : 0 < K) (t : WO S T) (ht : IsHalf E₂ t) :
    ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ u ∈ stdHom S T, IsHalf E₂ u ∧
      t = γ.map (fun a => E₂ * incA D a) + K • u := by
  obtain ⟨c, hc, hlat⟩ := exists_nsmul_mem_stdHom S T
  have hap : ∀ i j, ∃ γ : D.host.E, ∃ w ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      toEAf D (t i j) = eToEAf D γ + (K * c) • w := fun i j => exists_rat_add_nsmul _ (K * c) (Nat.mul_pos hK hc)
  choose γ w hw heq using hap
  choose y hy using fun i j => GlobalTheory.LocMod.exists_toEAf_lift (w i j)
  have hidem := GlobalTheory.PlaceDatum.idemSum_mul_self hE
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum hE
  let m : WO S T := Matrix.of fun i j => E₂ * y i j
  refine ⟨Matrix.of γ, c • m, hlat m ?_ ?_, ?_, ?_⟩
  · ext i j
    simp only [m, Matrix.map_apply, Matrix.of_apply, map_mul, hinf, zero_mul, Matrix.zero_apply]
  · intro i j
    simp only [m, Matrix.of_apply, map_mul, hy]
    exact mul_mem (GlobalTheory.ExportSeries.toEAf_mem_intAf_of_idem hidem) (hw i j)
  · intro i j
    simp only [m, Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul]
    linear_combination ((c : AE D) * y i j) * hidem
  · ext i j
    have hfin : finPart D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
      have h0 : toEAf D (t i j - incA D (γ i j) - (K * c) • y i j) = 0 := by
        rw [map_sub, map_sub, nsmul_eq_mul, map_mul, map_natCast, GlobalTheory.IdemIntegral.toEAf_incA, hy, heq i j,
          nsmul_eq_mul]
        abel
      unfold toEAf at h0
      rw [RingHom.comp_apply] at h0
      exact (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective (h0.trans (map_zero _).symm)
    have hz := mul_eq_zero_of_parts hinf hfin
    rw [mul_sub, mul_sub, sub_sub, sub_eq_zero, ht i j] at hz
    simp only [Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, m, Matrix.of_apply]
    rw [hz]
    congr 1
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

theorem eq_of_rat : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q →
    ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ →
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  intro D S T Q E₂ hE Φ₁ Φ₂ h₁ h₂ hrat
  obtain ⟨s₁, k₁, hk₁, inv₁, -⟩ := h₁
  obtain ⟨s₂, k₂, hk₂, inv₂, -⟩ := h₂
  funext t
  by_cases ht : IsHalf E₂ t
  · obtain ⟨γ, u, hu, huh, rfl⟩ := exists_half_approx hE (k₁ * k₂) (Nat.mul_pos hk₁ hk₂) t ht
    have half_smul : ∀ n : ℕ, IsHalf E₂ (n • u) := fun n i j => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, huh i j]
    have e1 : Φ₁ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₁ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_smul]
      exact inv₁ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    have e2 : Φ₂ (γ.map (fun a => E₂ * incA D a) + (k₁ * k₂) • u) = Φ₂ (γ.map (fun a => E₂ * incA D a)) := by
      rw [mul_comm, mul_smul]
      exact inv₂ _ (AddSubgroup.nsmul_mem _ hu _) (half_smul _) _
    rw [e1, e2, hrat]
  · have a1 : Φ₁ t = 0 := by
      by_contra h
      exact ht (s₁ t h)
    have a2 : Φ₂ t = 0 := by
      by_contra h
      exact ht (s₂ t h)
    rw [a1, a2]

end GlobalTheory.RatHalfDense
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfEqOfEqOnRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_half_eq_of_eq_on_rational : ∀ (D : D7) (S T : HSp D) (Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (E₂ : AE D), IsIdemSum E₂ Q → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf E₂ (stdHom S T) Φ₁ → IsSBHalf E₂ (stdHom S T) Φ₂ → (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ₁ (γ.map fun a => E₂ * incA D a) = Φ₂ (γ.map fun a => E₂ * incA D a)) → Φ₁ = Φ₂ := by
  first | exact @GlobalTheory.RatHalfDense.eq_of_rat | exact GlobalTheory.RatHalfDense.eq_of_rat | (intros; apply GlobalTheory.RatHalfDense.eq_of_rat <;> assumption)
end
end
