module

public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericCommutationOfReorder
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.CosetMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMem
noncomputable section
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD GlobalTheory.ThetaPull GlobalTheory.SmGL

namespace GlobalTheory.CompanionTheory.DualSm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem map_invT {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (invT a R g) = invT a S (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  change p ((g⁻¹).val j i) = (GeneralLinearGroup.map p g)⁻¹.val j i
  rw [← map_inv]
  rfl

theorem invA_infGL (y : GL (Fin a) (Cinf E)) :
    invA E a (infGL E a y) = infGL E a (invT a (Cinf E) y) :=
  ga_ext (by rw [invA, map_invT, pInf_infGL, pInf_infGL])
    (by rw [invA, map_invT, pFin_infGL, pFin_infGL, map_one])


omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
def trL : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => toL (Matrix.of X)ᵀ
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }


omit [_root_.NumberField.IsTotallyComplex E] in
theorem toL_invT (y : GL (Fin a) (Cinf E)) : toL (invT a (Cinf E) y).val = trL (invL (toL y.val)) := by
  change toL ((y⁻¹).val)ᵀ = toL (Matrix.of (toL (Matrix.of (toL y.val))⁻¹))ᵀ
  rw [Matrix.coe_units_inv]
  rfl

theorem chart_dual (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun g => star (φ (invA E a g))) g x = star (chart φ (invA E a g) (trL (invL x))) ∧
      trL (invL x) ∈ invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  rw [← toL_invT, chart_val, chart_val, map_mul, invA_infGL]
  exact ⟨rfl, val_mem_invSet _⟩

theorem conj_invA_mem_Sm {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) :
    (fun g => star (φ (invA E a g))) ∈ Sm E a := fun g =>
  (Complex.conjCLE.contDiff.comp_contDiffOn ((hφ (invA E a g)).comp
    (fun x hx => (trL.contDiff.contDiffAt.comp x (invL_smooth.1 x hx)).contDiffWithinAt)
    fun _ hx => (chart_dual φ g hx).2)).congr fun _ hx => (chart_dual φ g hx).1

end GlobalTheory.CompanionTheory.DualSm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothConjugateInverseMemStatement
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec PositivityTheory.PRW.GKD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_conjugate_inverse_mem : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ {φ : GA E a → ℂ}, φ ∈ Sm E a → (fun g => star (φ (invA E a g))) ∈ Sm E a := by
  first | exact @GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | exact GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm | (intros; apply GlobalTheory.CompanionTheory.DualSm.conj_invA_mem_Sm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtension
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtension
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

namespace GlobalTheory.CompanionTheory.HeckeChar

theorem exists_unit_model : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  intro E Ω _ _ _ _ _ l _ μ hμ w A _ O _ _ _ Bw
  have hc : Continuous fun g : G E Ω => ((μ g : (Qbar l)ˣ) : Qbar l) := Units.continuous_val.comp hμ
  have hent : ∀ (g : G E Ω) (i j : Fin 1),
      ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) i j = ((μ g : (Qbar l)ˣ) : Qbar l) := by
    intro g i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [rk1]
  have hr : Continuous (fun g : G E Ω => ((rk1 μ g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l))) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    exact hc.congr fun g => (hent g i j).symm
  obtain ⟨L, hle, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (G E Ω) 1 (rk1 μ) hr Bw.LL
  have hmem : ∀ g : G E Ω, ((μ g : (Qbar l)ˣ) : Qbar l) ∈ L.1 := fun g => by
    have h := hL g 0 0
    rwa [hent] at h
  let ψ : ↥(Dec (F := E) A) →* (↥L.1)ˣ :=
    { toFun := fun g =>
        ⟨⟨((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          ⟨((μ ((g : G E Ω)⁻¹) : (Qbar l)ˣ) : Qbar l), hmem _⟩,
          Subtype.ext (by simp [← Units.val_mul, ← map_mul]),
          Subtype.ext (by simp [← Units.val_mul, ← map_mul])⟩
      map_one' := Units.ext (Subtype.ext (by simp))
      map_mul' := fun g h => Units.ext (Subtype.ext (by simp)) }
  have hψ : ∀ g, ((ψ g : ↥L.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l) := fun g => rfl
  refine ⟨L, ψ, hle, ⟨hle, ?_⟩, hψ, ?_, fun g => ?_⟩
  · refine MonoidHom.ext fun g => Units.ext ?_
    ext i j
    have hij : i = j := Subsingleton.elim i j
    subst hij
    simp [Formalism.MainNotions.N.mapRep, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, rk1, hψ]
  · exact hc.comp continuous_subtype_val
  · exact GlobalTheory.ExpFrame.CharUnit.norm_eq_one_of_compact μ hc _

end GlobalTheory.CompanionTheory.HeckeChar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalCharacterFiniteExtensionStatement
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_character_finite_extension : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (μ : G E Ω →* (Qbar l)ˣ), Continuous μ →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
    ∃ (LL' : FinExt l) (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ), Bw.LL.1 ≤ LL'.1 ∧
      IsModel Bw ((rk1 μ).comp (Dec (F := E) A).subtype) LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ) ∧
      (∀ g, ((ψ g : ↥LL'.1) : Qbar l) = ((μ (g : G E Ω) : (Qbar l)ˣ) : Qbar l)) ∧
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) ∧ ∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | exact GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model | (intros; apply GlobalTheory.CompanionTheory.HeckeChar.exists_unit_model <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMemKNInvMulMemInfMapConj
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_mem_KN_inv_mul_mem_inf_map_conj
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∀ y ∈ J,
      ∃ a ∈ KN k N J d hd, a⁻¹ * y ∈
        J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro _ _ hfact _ t hdom y hy
  obtain ⟨-, hNl, hM⟩ := hdom
  obtain ⟨u, hu, b, hb, n, hn, hyf⟩ := hfact y⁻¹ (J.inv_mem hy)
  obtain ⟨huJ, -⟩ := Subgroup.mem_inf.1 hu
  obtain ⟨hbJ, x, rfl⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hnJ, hnN⟩ := Subgroup.mem_inf.1 hn
  have hy' : y = n⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    have : y = (y⁻¹)⁻¹ := (inv_inv y).symm
    rw [this, hyf]; group
  refine ⟨n⁻¹, (KN k N J d hd).inv_mem (Subgroup.mem_inf.2 ⟨hnJ, hnN⟩), ?_⟩
  have hred : (n⁻¹)⁻¹ * y = (leviEmb k (stdBlocks d hd) x)⁻¹ * u⁻¹ := by
    rw [hy']; group
  rw [hred]
  set g := leviEmb k (stdBlocks d hd) t with hg
  have hxKM : x⁻¹ ∈ KM k N J d hd :=
    (KM k N J d hd).inv_mem (show x ∈ (J).comap (leviEmb k (stdBlocks d hd)) from hbJ)
  have h1 : g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g ∈ J := by
    have h2 : t⁻¹ * x⁻¹ * t ∈ KM k N J d hd := (hM _ hxKM).2
    have h3 : leviEmb k (stdBlocks d hd) (t⁻¹ * x⁻¹ * t) ∈ J := h2
    simpa [hg, map_mul, map_inv] using h3
  have h4 : g⁻¹ * u⁻¹ * g ∈ J :=
    (Subgroup.mem_inf.1 (hNl _ ((KNl k N J d hd).inv_mem hu))).1
  refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.inv_mem hbJ) (J.inv_mem huJ), ?_⟩
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * (leviEmb k (stdBlocks d hd) x)⁻¹ * g) * (g⁻¹ * u⁻¹ * g),
    J.mul_mem h1 h4, ?_⟩
  simp only [MonoidHom.coe_coe, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetReps
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Casselman

theorem exists_fin_KN_coset_reps
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)) :
    IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) →
    HasIwahoriFact k N J d hd → (∀ a, 0 < d a) →
    ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧
      ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧
        ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈
          J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  intro hJo hJc hIw hpos t hdom
  have hKN : KN k N J d hd ≤ J := inf_le_left
  exact GlobalTheory.CompanionTheory.CosetReps.exists_fin_coset_reps (GL (Fin N) k) J
    (J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom) (KN k N J d hd) hJc
    (GlobalTheory.CompanionTheory.TopGroup.inter_conj_isOpen _ J hJo _) inf_le_left hKN
    (exists_mem_KN_inv_mul_mem_inf_map_conj k N h d hd J hJo hJc hIw hpos t hdom)

end GlobalTheory.CompanionTheory.Casselman
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantIwahoriCosetRepsStatement
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_iwahori_coset_reps : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N h : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (J : Subgroup (GL (Fin N) k)), IsOpen (J : Set (GL (Fin N) k)) → IsCompact (J : Set (GL (Fin N) k)) → HasIwahoriFact k N J d hd → (∀ a, 0 < d a) → ∀ t : Levi k (Bl d), IsDominant k N J d hd t → ∃ r : ℕ, 0 < r ∧ ∃ x : Fin r → GL (Fin N) k, (∀ i, x i ∈ KN k N J d hd) ∧ ∀ y ∈ J, ∃! i, (x i)⁻¹ * y ∈ J ⊓ J.map (MulAut.conj (leviEmb k (stdBlocks d hd) t)).toMonoidHom := by
  first | exact @GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | exact GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps | (intros; apply GlobalTheory.CompanionTheory.Casselman.exists_fin_KN_coset_reps <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorph
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorph
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.LeviIso

theorem leviEquiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  intro k _ _ _ _ α _ _ N m _ _ e β hβ
  have hz : ∀ x : GL (Fin N) k, x ∈ levi k N β → ∀ i j : Fin N, blk e i ≠ blk e j →
      (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro x hx i j hij
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper] at hx
    rcases lt_or_gt_of_ne hij with h | h
    · exact hx.2 (OrderDual.toDual_lt_toDual.mpr ((hβ i j).2 h))
    · exact hx.1 ((hβ j i).2 h)
  have hzE : ∀ (g : Levi k m) (i j : Fin N), blk e i ≠ blk e j →
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro g i j hij
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    have hab : a ≠ b := by simpa [blk] using hij
    exact leviEmb_apply_ne k e g hab i' j'
  have hent : ∀ (g : Levi k m) (a : α) (i j : m a),
      ((leviEmb k e g : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (e ⟨a, i⟩) (e ⟨a, j⟩) =
        ((g a : GL (m a) k) : Matrix (m a) (m a) k) i j := by
    intro g a i j
    exact leviEmb_apply_same k e g a i j
  have hmem : ∀ g : Levi k m, leviEmb k e g ∈ levi k N β := by
    intro g
    simp only [levi, Subgroup.mem_inf, GroundTheory.Automorphic.Iwasawa.mem_blockUpper]
    constructor
    · intro i j h
      exact hzE g i j ((hβ j i).1 h).ne'
    · intro i j h
      exact hzE g i j ((hβ i j).1 (OrderDual.toDual_lt_toDual.1 h)).ne
  have hkey : ∀ x : GL (Fin N) k, x ∈ levi k N β →
      Matrix.blockDiagonal' (Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e)) =
        (x : Matrix (Fin N) (Fin N) k).submatrix e e := by
    intro x hx
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases hab : a = b
    · subst hab
      rw [Matrix.blockDiagonal'_apply_eq, Matrix.blockDiag'_apply]
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hab, Matrix.submatrix_apply,
        hz x hx _ _ (by simpa [blk] using hab)]
  have hmul : ∀ x y : GL (Fin N) k, x ∈ levi k N β → y ∈ levi k N β → ∀ a : α,
      Matrix.blockDiag' ((x : Matrix (Fin N) (Fin N) k).submatrix e e) a *
          Matrix.blockDiag' ((y : Matrix (Fin N) (Fin N) k).submatrix e e) a =
        Matrix.blockDiag' (((x * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a := by
    intro x y hx hy a
    rw [Units.val_mul, ← Matrix.submatrix_mul_equiv (x : Matrix (Fin N) (Fin N) k)
      (y : Matrix (Fin N) (Fin N) k) e e e, ← hkey x hx, ← hkey y hy]
    simp only [← Matrix.blockDiagonal'_mul, Matrix.blockDiag'_blockDiagonal']
  have hcont : ∀ f : Levi k m → Levi k m,
      (∀ a, Continuous fun g => ((f g a : GL (m a) k) : Matrix (m a) (m a) k)) →
        Continuous fun g => ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := by
    intro f hf
    refine continuous_matrix fun i j => ?_
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      simp only [hent]
      exact (hf a).matrix_elem i' j'
    · have h0 : ∀ g, ((leviEmb k e (f g) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k)
          (e ⟨a, i'⟩) (e ⟨b, j'⟩) = 0 := fun g => hzE _ _ _ (by simpa [blk] using hab)
      simp only [h0]
      exact continuous_const
  have hLE : Continuous (leviEmb k e) := continuous_leviEmb k e
  let ψ : levi k N β → Levi k m := fun x => (fun a =>
      ⟨Matrix.blockDiag' (((x : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        Matrix.blockDiag' ((((x : GL (Fin N) k)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).submatrix e e) a,
        by rw [hmul _ _ x.2 (inv_mem x.2), mul_inv_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl,
        by rw [hmul _ _ (inv_mem x.2) x.2, inv_mul_cancel, Units.val_one,
          Matrix.submatrix_one_equiv, Matrix.blockDiag'_one]; rfl⟩ : ∀ a, GL (m a) k)
  refine ⟨{
      toFun := fun g => ⟨leviEmb k e g, hmem g⟩
      invFun := ψ
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }, fun g => rfl, ?_, ?_⟩
  · intro g
    refine funext fun a => ?_
    apply Units.ext
    ext i j
    simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    exact hent g a i j
  · intro x
    apply Subtype.ext
    apply Units.ext
    ext i j
    obtain ⟨⟨a, i'⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j'⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      dsimp only
      rw [hent]
      simp only [ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
    · have h' : blk e (e ⟨a, i'⟩) ≠ blk e (e ⟨b, j'⟩) := by simpa [blk] using hab
      dsimp only
      rw [hzE _ _ _ h', hz _ x.2 _ _ h']
  · intro g h
    apply Subtype.ext
    exact map_mul (leviEmb k e) g h
  · exact hLE.subtype_mk hmem
  · change Continuous ψ
    refine continuous_pi fun a => ?_
    rw [Units.continuous_iff]
    constructor
    · refine continuous_matrix fun i j => ?_
      simp only [Function.comp_apply, ψ, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem _ _
    · refine continuous_matrix fun i j => ?_
      simp only [ψ, Units.inv_mk, Matrix.blockDiag'_apply, Matrix.submatrix_apply]
      exact (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem _ _

end GlobalTheory.CompanionTheory.LeviIso
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockHomeomorphStatement
set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_block_homeomorph : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α : Type} [Fintype α] [LinearOrder α] {N : ℕ} {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] (e : (Σ i, m i) ≃ Fin N) (β : Fin N → ℕ), (∀ x y, β x < β y ↔ blk e x < blk e y) → ∃ φ : Levi k m ≃* levi k N β, (∀ g, ((φ g : levi k N β) : GL (Fin N) k) = leviEmb k e g) ∧ Continuous φ ∧ Continuous φ.symm := by
  first | exact @GlobalTheory.CompanionTheory.LeviIso.leviEquiv | exact GlobalTheory.CompanionTheory.LeviIso.leviEquiv | (intros; apply GlobalTheory.CompanionTheory.LeviIso.leviEquiv <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableT2LocalField
open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.GLMeasure

open ValuativeRel

theorem secondCountable_t2_local_field (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SecondCountableTopology k ∧ T2Space k := by
  letI := IsTopologicalAddGroup.rightUniformSpace k
  haveI := isUniformAddGroup_of_addCommGroup (G := k)
  letI : (Valued.v (R := k)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  haveI : ProperSpace k := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace k
  exact ⟨secondCountable_of_proper, inferInstance⟩

theorem secondCountable_GL (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) : SecondCountableTopology (GL (Fin n) k) := by
  obtain ⟨_, _⟩ := secondCountable_t2_local_field k
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → k))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) k)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) k)).secondCountableTopology

end GlobalTheory.CompanionTheory.GLMeasure
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupport
open MeasureTheory PositivityTheory.Rg.Tf.Loc
open scoped ENNReal Topology

namespace GlobalTheory.CompanionTheory.QuotU

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

def coset (U : Subgroup G) (r : G) : Set G := {x | r⁻¹ * x ∈ U}

theorem isOpen_coset {U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) : IsOpen (coset U r) :=
  hU.preimage (continuous_const.mul continuous_id)

theorem mem_coset_self (U : Subgroup G) (r : G) : r ∈ coset U r := by
  simp [coset, U.one_mem]

def conjSet (H U : Subgroup G) (r : G) : Set H := {h | r⁻¹ * (h : G) * r ∈ U}

theorem isOpen_conjSet {H U : Subgroup G} (hU : IsOpen (U : Set G)) (r : G) :
    IsOpen (conjSet H U r) :=
  hU.preimage ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem one_mem_conjSet (H U : Subgroup G) (r : G) : (1 : H) ∈ conjSet H U r := by
  simp [conjSet, U.one_mem]

theorem isCompact_conjSet {H U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hH : IsClosed (H : Set G)) (r : G) : IsCompact (conjSet H U r) := by
  have hK : IsCompact ((fun u => r * u * r⁻¹) '' (U : Set G)) :=
    hUc.image (by fun_prop)
  have hs : conjSet H U r = Subtype.val ⁻¹' ((fun u => r * u * r⁻¹) '' (U : Set G)) := by
    ext h
    constructor
    · intro hh
      exact ⟨_, hh, by group⟩
    · rintro ⟨u, hu, e⟩
      have e' : r⁻¹ * (h : G) * r = u := by
        have e2 : r * u * r⁻¹ = (h : G) := e
        rw [← e2]; group
      show r⁻¹ * (h : G) * r ∈ U
      rw [e']; exact hu
  rw [hs]
  exact hH.isClosedEmbedding_subtypeVal.isCompact_preimage hK

theorem rep_eq_of_mem {H U : Subgroup G} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r r' x : G} (hr : r ∈ Rp) (hr' : r' ∈ Rp) (hx : x ∈ coset U r) (hx' : x ∈ coset U r') :
    r = r' := by
  have h1 : r⁻¹ * x ∈ U := hx
  have h2 : r'⁻¹ * x ∈ U := hx'
  refine huniq r hr r' hr' ⟨1, H.one_mem, (r⁻¹ * x) * (r'⁻¹ * x)⁻¹,
    U.mul_mem h1 (U.inv_mem h2), by group⟩

theorem countable_reps [SecondCountableTopology G] {H U : Subgroup G} {Rp : Set G}
    (hU : IsOpen (U : Set G))
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    Countable Rp := by
  have hd : Rp.PairwiseDisjoint (coset U) := by
    intro r hr r' hr' hne
    refine Set.disjoint_left.mpr fun x hx hx' => hne ?_
    exact rep_eq_of_mem huniq hr hr' hx hx'
  exact (hd.countable_of_isOpen (fun r _ => isOpen_coset hU r)
    (fun r _ => ⟨r, mem_coset_self U r⟩)).to_subtype

variable [MeasurableSpace G] [BorelSpace G]

noncomputable def rho {H : Subgroup G} (μH : Measure H) (U : Subgroup G) (Rp : Set G) (g : G) :
    ℝ≥0∞ :=
  ∑' r : Rp, (coset U (r : G)).indicator (fun _ => (μH (conjSet H U r))⁻¹) g

theorem rho_of_mem {H U : Subgroup G} {μH : Measure H} {Rp : Set G}
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r')
    {r x : G} (hr : r ∈ Rp) (hx : x ∈ coset U r) :
    rho μH U Rp x = (μH (conjSet H U r))⁻¹ := by
  rw [rho, tsum_eq_single (⟨r, hr⟩ : Rp)]
  · exact Set.indicator_of_mem hx _
  · intro r' hne
    refine Set.indicator_of_notMem (fun hx' => hne ?_) _
    exact Subtype.ext (rep_eq_of_mem huniq r'.2 hr hx' hx)

theorem rho_of_notMem {H U : Subgroup G} {μH : Measure H} {Rp : Set G} {x : G}
    (hx : ∀ r ∈ Rp, x ∉ coset U r) : rho μH U Rp x = 0 := by
  rw [rho]
  convert tsum_zero with r
  exact Set.indicator_of_notMem (hx r r.2) _

theorem measurable_rho {H U : Subgroup G} {μH : Measure H} {Rp : Set G} [Countable Rp]
    (hU : IsOpen (U : Set G)) : Measurable (rho μH U Rp) := by
  refine Measurable.tsum fun r => ?_
  exact measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet

theorem rho_isQuotNormaliser [SecondCountableTopology G] {H U : Subgroup G} {μH : Measure H}
    [μH.IsHaarMeasure] {Rp : Set G}
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) (hH : IsClosed (H : Set G))
    (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    IsQuotNormaliser H μH (rho μH U Rp) := by
  haveI : Countable Rp := countable_reps hU huniq
  refine ⟨measurable_rho hU, fun g => ?_⟩
  obtain ⟨r, hr, h0, hh0, κ, hκ, rfl⟩ := hcov g
  have hpos : μH (conjSet H U r) ≠ 0 :=
    ((isOpen_conjSet hU r).measure_pos μH ⟨1, one_mem_conjSet H U r⟩).ne'
  have htop : μH (conjSet H U r) ≠ ∞ := (isCompact_conjSet hUc hH r).measure_lt_top.ne
  have hiff : ∀ h : H, (h : G) * (h0 * r * κ) ∈ coset U r ↔
      (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r := by
    intro h
    have e : r⁻¹ * ((h : G) * (h0 * r * κ)) = (r⁻¹ * (h0 * (h : G)) * r) * κ := by
      rw [show (h : G) * (h0 * r * κ) = ((h : G) * h0) * r * κ by group, hcomm _ h.2 _ hh0]
      group
    show r⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U ↔ r⁻¹ * (h0 * (h : G)) * r ∈ U
    rw [e]
    exact U.mul_mem_cancel_right hκ
  have hS : (fun h : H => rho μH U Rp ((h : G) * (h0 * r * κ))) =
      ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r).indicator
        (fun _ => (μH (conjSet H U r))⁻¹) := by
    funext h
    by_cases hm : (⟨h0, hh0⟩ * h : H) ∈ conjSet H U r
    · rw [Set.indicator_of_mem (show h ∈ _ from hm)]
      exact rho_of_mem huniq hr ((hiff h).mpr hm)
    · rw [Set.indicator_of_notMem (show h ∉ _ from hm)]
      refine rho_of_notMem fun r' hr' hx => hm ((hiff h).mp ?_)
      have hu : r'⁻¹ * ((h : G) * (h0 * r * κ)) ∈ U := hx
      have := huniq r hr r' hr' ⟨(h : G) * h0, H.mul_mem h.2 hh0,
        κ * (r'⁻¹ * ((h : G) * (h0 * r * κ)))⁻¹, U.mul_mem hκ (U.inv_mem hu), by group⟩
      rw [← this] at hx; exact hx
  have hmeas : MeasurableSet ((fun h : H => (⟨h0, hh0⟩ : H) * h) ⁻¹' conjSet H U r) :=
    ((isOpen_conjSet hU r).preimage (continuous_const.mul continuous_id)).measurableSet
  rw [hS, lintegral_indicator_const hmeas, measure_preimage_mul]
  exact ENNReal.inv_mul_cancel hpos htop

theorem measurable_of_right_invariant {U : Subgroup G} (hU : IsOpen (U : Set G))
    {Fn : G → ℝ≥0∞} (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) : Measurable Fn := by
  intro s _
  refine IsOpen.measurableSet (isOpen_iff_mem_nhds.mpr fun x hx => ?_)
  refine Filter.mem_of_superset ((isOpen_coset hU x).mem_nhds (mem_coset_self U x)) ?_
  intro y hy
  have : Fn (x * (x⁻¹ * y)) = Fn x := hFU x _ hy
  rw [mul_inv_cancel_left] at this
  show Fn y ∈ s
  rw [this]; exact hx

theorem quotLIntegral_eq_tsum [SecondCountableTopology G] [T2Space G]
    (μG : Measure G) (H : Subgroup G) (μH : Measure H) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hUc : IsCompact (U : Set G)) [μG.IsHaarMeasure]
    (hH : IsClosed (H : Set G)) (hcomm : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) [μH.IsHaarMeasure]
    (Fn : G → ℝ≥0∞) (hFH : ∀ h ∈ H, ∀ g, Fn (h * g) = Fn g)
    (hFU : ∀ g, ∀ κ ∈ U, Fn (g * κ) = Fn g) (Rp : Set G)
    (hcov : ∀ g, ∃ r ∈ Rp, ∃ h ∈ H, ∃ κ ∈ U, g = h * r * κ)
    (huniq : ∀ r ∈ Rp, ∀ r' ∈ Rp, (∃ h ∈ H, ∃ κ ∈ U, r' = h * r * κ) → r = r') :
    quotLIntegral μG H μH Fn =
      ∑' r : Rp, Fn r * μG (U : Set G) / μH {h : H | (r : G)⁻¹ * (h : G) * r ∈ U} := by
  haveI : LocallyCompactSpace G :=
    hUc.locallyCompactSpace_of_mem_nhds_of_group (hU.mem_nhds U.one_mem)
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : Countable Rp := countable_reps hU huniq
  haveI : μH.IsInvInvariant := by
    letI : CommGroup H := { (inferInstance : Group H) with
      mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
    haveI : μH.Regular := inferInstance
    exact Measure.IsHaarMeasure.isInvInvariant_of_regular μH
  have hFm : Measurable Fn := measurable_of_right_invariant hU hFU
  rw [quotLIntegral_eq hFm hFH (rho_isQuotNormaliser hU hUc hH hcomm hcov huniq)]
  have hpt : ∀ g, Fn g * rho μH U Rp g =
      ∑' r : Rp, (coset U (r : G)).indicator
        (fun _ => Fn r * (μH (conjSet H U r))⁻¹) g := by
    intro g
    rw [rho, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun r => ?_
    by_cases hg : g ∈ coset U (r : G)
    · have e : Fn ((r : G) * ((r : G)⁻¹ * g)) = Fn r := hFU _ _ hg
      rw [mul_inv_cancel_left] at e
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, e]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, mul_zero]
  rw [lintegral_congr hpt, lintegral_tsum]
  · refine tsum_congr fun r => ?_
    have hms : MeasurableSet (coset U (r : G)) := (isOpen_coset hU (r : G)).measurableSet
    have hvol : μG (coset U (r : G)) = μG (U : Set G) :=
      measure_preimage_mul μG (r : G)⁻¹ (U : Set G)
    rw [lintegral_indicator_const hms, hvol, div_eq_mul_inv, mul_right_comm]
    rfl
  · intro r
    exact (measurable_const.indicator (isOpen_coset hU (r : G)).measurableSet).aemeasurable

end Abstract

theorem h2U : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  intro F _ _ _ _ n _ _ μG H μH U hUo hUc hμG hH hcomm hμH Fn hFH hFU Rp hcov huniq
  haveI := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_GL F n
  obtain ⟨_, _⟩ := GlobalTheory.CompanionTheory.GLMeasure.secondCountable_t2_local_field F
  haveI : T2Space (Matrix (Fin n) (Fin n) F) := inferInstanceAs (T2Space (Fin n → Fin n → F))
  haveI : T2Space (GL (Fin n) F) := inferInstance
  exact quotLIntegral_eq_tsum μG H μH U hUo hUc hH hcomm Fn hFH hFU Rp hcov huniq

end GlobalTheory.CompanionTheory.QuotU
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentHeckeSupportStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_hecke_support : PositivityTheory.Rg.Tf.Loc.QuotientIntegralCompactOpen := by
  first | exact @GlobalTheory.CompanionTheory.QuotU.h2U | exact GlobalTheory.CompanionTheory.QuotU.h2U | (intros; apply GlobalTheory.CompanionTheory.QuotU.h2U <;> assumption)
end
end
