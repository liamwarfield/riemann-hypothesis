module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NodeAgree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountedVectorIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SobolevFormEqZeroOnSmoothOfKFiniteDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCoset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7}

theorem prod_eq_inf (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) = P.inf fun w => w.asIdeal ^ d w :=
  (HeightOneSpectrum.inf_pow_eq_prod _ _ _ fun _ _ _ _ hne h => hne h).symm

theorem prod_ne_bot (P : Finset (Pl D.host.E)) (d : Pl D.host.E → ℕ) :
    (∏ w ∈ P, w.asIdeal ^ d w) ≠ ⊥ := by
  rw [← Ideal.zero_eq_bot]
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact w.ne_bot)

theorem idem_mem_OA {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) : toEAf D e ∈ OA D := by
  obtain ⟨-, e1, e2⟩ := cpt_idemSum he
  refine (mem_OA_iff _).2 fun w => ?_
  by_cases hw : w ∈ P
  · rw [e1 w hw]; exact one_mem _
  · rw [e2 w hw]; exact zero_mem _

theorem one_sub_idem_mem {e : AE D} {P : Finset (Pl D.host.E)} (he : IsIdemSum e P) (d : Pl D.host.E → ℕ) :
    (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w) := by
  obtain ⟨-, e1, -⟩ := cpt_idemSum he
  refine mem_idS_of_v_le (w := fun w => w) (prod_ne_bot P d) (prod_eq_inf P d) fun w hw => ?_
  show Valued.v (cpt (D := D) w (1 - toEAf D e)) ≤ _
  rw [RingHom.map_sub, RingHom.map_one, e1 w hw, sub_self, Valuation.map_zero]
  exact zero_le'

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_map (hx : IsHalf e x) : x.map (toEAf D) = toEAf D e • x.map (toEAf D) :=
  Matrix.ext fun i j => by
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    rw [← RingHom.map_mul, hx i j]

theorem fr_half (hx : IsHalf e x) (i : Fin T.V.rank) (j : Fin S.V.rank) :
    fr T.β S.β (x.map (toEAf D)) i j = toEAf D e * fr T.β S.β (x.map (toEAf D)) i j := by
  have h1 : fr T.β S.β (x.map (toEAf D)) i j = fr T.β S.β (toEAf D e • x.map (toEAf D)) i j := by
    rw [← half_map hx]
  rw [fr_smul, Matrix.smul_apply, smul_eq_mul] at h1
  exact h1

variable {S T : GlobalTheory.Grid.Node D}

theorem frMapO_eq_fr (x : WO S.V T.V) : frMapO S.V T.V S.β T.β x = fr T.β S.β (x.map (toEAf D)) := by
  unfold frMapO fr
  rfl

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

theorem alg_one {R : Type} [CommRing R] {s t A A' X Y E eS : R} (hs : s = E * (X - Y)) (ht : t = Y - A') (ha : A = A')
    (he : eS = E) (hx : X = E * X) : s + eS * t - (1 - eS) * A + A = X := by
  subst hs ht ha he
  linear_combination -hx

theorem alg_two {R : Type} [CommRing R] {s t A X eS : R} (h : s + eS * t - (1 - eS) * A + A = X) :
    X - A = s + eS * t - (1 - eS) * A := by
  rw [← h]; ring

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}

theorem half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : (x - e • y.map (incA D)) i j = e * (x i j - incA D (y i j)) := by
  rw [mul_sub, hx]; rfl

theorem fr_half_sub (hx : IsHalf e x) (y : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E) (i : Fin T.V.rank)
    (j : Fin S.V.rank) : fr T.β S.β ((x - e • y.map (incA D)).map (toEAf D)) i j =
      toEAf D e * (fr T.β S.β (x.map (toEAf D)) i j - fr T.β S.β (y.map (eToEAf D)) i j) := by
  have h : (x - e • y.map (incA D)).map (toEAf D) = toEAf D e • (x.map (toEAf D) - y.map (eToEAf D)) :=
    Matrix.ext fun i j => by rw [Matrix.map_apply, half_sub hx, RingHom.map_mul, RingHom.map_sub]; rfl
  rw [h, fr_smul, fr_sub]; rfl

theorem sub_mem_hatMx {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ)
    (he : IsIdemSum e P) (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x)
    (h : ∀ i j, ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I) :
    x - e • (x₀.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ) := by
  obtain ⟨e0, -, -⟩ := cpt_idemSum he
  refine (mem_hatMx_iff hS hT _ _).2 ⟨fun i j => by rw [half_sub hx, RingHom.map_mul, e0, zero_mul], fun i j => ?_⟩
  obtain ⟨hX, h'⟩ := h i j
  refine ⟨⟨toEAf D e, idem_mem_OA he⟩ * (⟨_, hX⟩ - a i j), Ideal.mul_mem_left _ _ h', ?_⟩
  refine Eq.trans ?_ (fr_half_sub hx x₀.1 i j).symm
  exact congrArg (toEAf D e * ·) (congrArg₂ (· - ·) rfl (ha i j))

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D} {x : WO S.V T.V}


set_option maxHeartbeats 1000000 in
theorem frMapO_sub_mem {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ) (hT : IsFrame T.β T.Λ) (eS : OA D)
    (heS : eS.1 = toEAf D e) (he1 : 1 - eS ∈ idS D.host.F I)
    (x₀ : homLat S.Λ T.Λ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (hx : IsHalf e x) (y : homLat S.Λ T.Λ)
    (hyx : y.1 - x₀.1 ∈ I • homLat S.Λ T.Λ)
    (hz : x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ))
    (i : Fin T.V.rank) (j : Fin S.V.rank) : ∃ hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E,
      (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I := by
  obtain ⟨s, hs, hs'⟩ := ((mem_hatMx_iff hS hT _ _).1 hz).2 i j
  obtain ⟨t, ht, ht'⟩ := fr_mem_idS hS hT hyx i j
  have hs'' := hs'.trans (fr_half_sub hx y.1 i j)
  have hyA : t.1 = fr T.β S.β (y.1.map (eToEAf D)) i j - fr T.β S.β (x₀.1.map (eToEAf D)) i j := by
    rw [ht', Matrix.map_sub _ (RingHom.map_sub _), fr_sub, Matrix.sub_apply]
  have hz0 : s.1 + eS.1 * t.1 - (1 - eS.1) * (a i j).1 + (a i j).1 = fr T.β S.β (x.map (toEAf D)) i j :=
    alg_one hs'' hyA (ha i j) heS (fr_half hx i j)
  have hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    have hz1 : ((s + eS * t - (1 - eS) * a i j + a i j : OA D) : EAf D) = fr T.β S.β (x.map (toEAf D)) i j := by
      simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
      exact hz0
    rw [frMapO_eq_fr, ← hz1]
    exact (s + eS * t - (1 - eS) * a i j + a i j).2
  refine ⟨hX, ?_⟩
  have : (⟨_, hX⟩ : OA D) - a i j = s + eS * t - (1 - eS) * a i j := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, OneMemClass.coe_one]
    rw [frMapO_eq_fr]
    exact alg_two hz0
  rw [this]
  exact sub_mem (add_mem hs (Ideal.mul_mem_left _ _ ht)) (Ideal.mul_mem_right _ _ he1)

end GlobalTheory.CosToCoset

namespace GlobalTheory.CosToCoset

open GlobalTheory.FunObj.Comparison₂ GlobalTheory.StdFrames

variable {D : D7} {S T : GlobalTheory.Grid.Node D} {e : AE D}


set_option maxHeartbeats 1000000 in
theorem cosetInd_eq_of {P : Finset (Pl D.host.E)} {I : Ideal (𝓞 D.host.E)} (hS : IsFrame S.β S.Λ)
    (hT : IsFrame T.β T.Λ) (he : IsIdemSum e P) (he1 : (1 - ⟨toEAf D e, idem_mem_OA he⟩ : OA D) ∈ idS D.host.F I)
    (κ : Cos S.Λ T.Λ I) (x₀ : homLat S.Λ T.Λ) (hx₀ : Cos.mk I x₀ = κ) (a : Fin T.V.rank → Fin S.V.rank → OA D)
    (ha : ∀ i j, (a i j).1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j) (c : Coset S T I)
    (hc : ∀ i j, cmpS D.host.F I (c i j) = Ideal.Quotient.mk (idS D.host.F I) (a i j)) :
    cosetInd S T e I c = cosInd e κ := by
  funext x
  have key : IsHalf e x → (InCosetOf S T I c x ↔ ∃ y : homLat S.Λ T.Λ, Cos.mk I y = κ ∧
      x - e • (y.1 : Matrix (Fin T.V.rank) (Fin S.V.rank) D.host.E).map (incA D) ∈ hatMx (I • homLat S.Λ T.Λ)) := by
    intro hx
    have hq : ∀ i j (hX : frMapO S.V T.V S.β T.β x i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E),
        Ideal.Quotient.mk (idS D.host.F I) ⟨_, hX⟩ = cmpS D.host.F I (c i j) ↔ (⟨_, hX⟩ : OA D) - a i j ∈ idS D.host.F I :=
      fun i j hX => by rw [hc i j, Ideal.Quotient.eq]
    constructor
    · intro h
      exact ⟨x₀, hx₀, sub_mem_hatMx hS hT he x₀ a ha hx fun i j => ⟨(h i j).1, (hq i j _).1 (h i j).2⟩⟩
    · rintro ⟨y, hy, hz⟩ i j
      obtain ⟨hX, h'⟩ := frMapO_sub_mem hS hT _ rfl he1 x₀ a ha hx y (sub_mem_of_mk_eq (hy.trans hx₀.symm)) hz i j
      exact ⟨hX, (hq i j hX).2 h'⟩
  have hiff : (IsHalf e x ∧ InCosetOf S T I c x) ↔ x ∈ cosSet e κ :=
    ⟨fun ⟨h1, h2⟩ => ⟨h1, (key h1).1 h2⟩, fun ⟨h1, h2⟩ => ⟨h1, (key h1).2 h2⟩⟩
  unfold GlobalTheory.Grid.cosetInd GlobalTheory.ChiGrid.cosInd
  by_cases h : x ∈ cosSet e κ
  · rw [if_pos (hiff.2 h), Set.indicator_of_mem h]; rfl
  · rw [if_neg (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]

theorem cosInd_eq_cosetInd : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  intro D S T e P d hS hT he κ
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : homLat S.Λ T.Λ, Cos.mk (∏ w ∈ P, w.asIdeal ^ d w) x₀ = κ :=
    Submodule.Quotient.mk_surjective _ κ
  have hA : ∀ i j, ∃ s : OA D, s.1 = fr T.β S.β (x₀.1.map (eToEAf D)) i j := fun i j => by
    obtain ⟨s, -, hs⟩ := fr_mem_idS hS hT (𝔪 := ⊤) (y := x₀.1) (by rw [Submodule.top_smul]; exact x₀.2) i j
    exact ⟨s, hs⟩
  choose a ha using hA
  choose c hc using fun i j => cmpS_surj (F := D.host.F) _ (prod_ne_bot P d)
    (Ideal.Quotient.mk (idS D.host.F (∏ w ∈ P, w.asIdeal ^ d w)) (a i j))
  exact ⟨fun i j => c i j, cosetInd_eq_of hS hT he (one_sub_idem_mem he d) κ x₀ hx₀ a ha _ fun i j => hc i j⟩

end GlobalTheory.CosToCoset
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomLatticeCosetIndicatorEqLatticeHomCosetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homLatticeCosetIndicator_eq_latticeHomCoset : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (d : Formalism.L2.DIV.Pl D.host.E → ℕ), Formalism.L2.DIV.IsFrame S.β S.Λ → Formalism.L2.DIV.IsFrame T.β T.Λ → IsIdemSum e P → ∀ κ : GlobalTheory.ChiGrid.Cos S.Λ T.Λ (∏ w ∈ P, w.asIdeal ^ d w), ∃ c : GlobalTheory.Grid.Coset S T (∏ w ∈ P, w.asIdeal ^ d w), GlobalTheory.Grid.cosetInd S T e (∏ w ∈ P, w.asIdeal ^ d w) c = GlobalTheory.ChiGrid.cosInd e κ := by
  first | exact @GlobalTheory.CosToCoset.cosInd_eq_cosetInd | exact GlobalTheory.CosToCoset.cosInd_eq_cosetInd | (intros; apply GlobalTheory.CosToCoset.cosInd_eq_cosetInd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]

theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := fun V Λ hΛ => _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

theorem exists_basis_in_lattice {n : ℕ} (Λ : Submodule (𝓞 K) (Fin n → K)) [hΛ : Λ.IsFullLattice K] (N : ℕ) (hN : 2 ≤ N) :
    ∃ b : Module.Basis (Fin n) K (Fin n → K), (∀ i, b i ∈ Λ) ∧ ∃ c : 𝓞 K, IsCoprime c (N : 𝓞 K) ∧
      ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range b) := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ.fg
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  haveI : HasUniqueDiv Λ := ⟨fun k hk a b h => Subtype.ext
    (nsmul_right_injective hk (by simpa using congrArg Subtype.val h))⟩
  obtain ⟨r, x, hli, c, hc0, hcop, hspan⟩ := GlobalTheory.CoprimeBasis.exists_coprime_basis K Λ N hN
  set x' : Fin r → (Fin n → K) := fun i => (x i : Fin n → K) with hx'
  have hli' : LinearIndependent (𝓞 K) x' := hli.map' Λ.subtype (Submodule.ker_subtype Λ)
  have hliK : LinearIndependent K x' := (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hli'
  have hmem : ∀ w ∈ Λ, (c : K) • w ∈ Submodule.span (𝓞 K) (Set.range x') := by
    intro w hw
    have h := Submodule.mem_map_of_mem (f := Λ.subtype) (hspan ⟨w, hw⟩)
    rw [Submodule.map_span, ← Set.range_comp] at h
    have e : (Λ.subtype (c • (⟨w, hw⟩ : Λ))) = (c : K) • w := by
      simp [Submodule.coe_smul, algebraMap_smul]
    rw [e] at h
    exact h
  have hcK : (c : K) ≠ 0 := by exact_mod_cast hc0
  have hspanK : ⊤ ≤ Submodule.span K (Set.range x') := by
    rw [← hΛ.span_eq_top, Submodule.span_le]
    intro w hw
    have h1 := Submodule.span_le_restrictScalars (𝓞 K) K (Set.range x') (hmem w hw)
    have h2 := Submodule.smul_mem (Submodule.span K (Set.range x')) (c : K)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hcK, one_smul] at h2
  let b0 : Module.Basis (Fin r) K (Fin n → K) := Module.Basis.mk hliK hspanK
  have hr : r = n := by
    have := Module.finrank_eq_card_basis b0
    simpa using this.symm
  subst hr
  refine ⟨b0, fun i => ?_, c, hcop, fun w hw => ?_⟩
  · rw [Module.Basis.mk_apply]; exact (x i).2
  · have : Set.range b0 = Set.range x' := by rw [Module.Basis.coe_mk]
    rw [this]; exact hmem w hw

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField

variable {K : Type} [Field K] [NumberField K]


open Matrix in
theorem exists_onto_mod {n n' : ℕ} (hnn : n ≤ n') (Λ : Submodule (𝓞 K) (Fin n → K)) (Λ' : Submodule (𝓞 K) (Fin n' → K))
    [Λ.IsFullLattice K] [Λ'.IsFullLattice K] (𝔪 : Ideal (𝓞 K)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ x : Matrix (Fin n) (Fin n') K, (∀ w ∈ Λ', x *ᵥ w ∈ Λ) ∧ ∃ y : Matrix (Fin n') (Fin n) K, (∀ v ∈ Λ, y *ᵥ v ∈ Λ') ∧
      ∃ a ∈ 𝔪, x * y - 1 = (a : K) • (1 : Matrix (Fin n) (Fin n) K) := by
  classical
  set N : ℕ := 2 * Ideal.absNorm 𝔪 with hNdef
  have hN0 : Ideal.absNorm 𝔪 ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN : 2 ≤ N := by omega
  have hNm : (N : 𝓞 K) ∈ 𝔪 := by
    rw [hNdef, Nat.cast_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.absNorm_mem 𝔪)
  obtain ⟨b, hb, c, hc, hcb⟩ := exists_basis_in_lattice Λ N hN
  obtain ⟨b', hb', c', hc', hcb'⟩ := exists_basis_in_lattice Λ' N hN
  obtain ⟨u, v, huv⟩ := hc.mul_left hc'
  let φ : (Fin n' → K) →ₗ[K] (Fin n → K) := b'.constr K fun j => if h : (j : ℕ) < n then b ⟨j, h⟩ else 0
  let ψ : (Fin n → K) →ₗ[K] (Fin n' → K) := b.constr K fun i => b' (Fin.castLE hnn i)
  have hφψ : φ ∘ₗ ψ = LinearMap.id := by
    refine b.ext fun i => ?_
    show φ (ψ (b i)) = b i
    simp only [φ, ψ, Module.Basis.constr_basis, Fin.coe_castLE]
    rw [dite_eq_left i.isLt]
  have hφ : Submodule.span (𝓞 K) (Set.range b') ≤ Λ.comap (φ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show φ (b' j) ∈ Λ
    simp only [φ, Module.Basis.constr_basis]
    split_ifs
    · exact hb _
    · exact Λ.zero_mem
  have hψ : Submodule.span (𝓞 K) (Set.range b) ≤ Λ'.comap (ψ.restrictScalars (𝓞 K)) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show ψ (b i) ∈ Λ'
    simp only [ψ, Module.Basis.constr_basis]
    exact hb' _
  refine ⟨LinearMap.toMatrix' (((u * c' : 𝓞 K) : K) • φ), fun w hw => ?_,
    LinearMap.toMatrix' ((c : K) • ψ), fun w hw => ?_, u * c * c' - 1, ?_, ?_⟩
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply]
    have h1 : φ ((c' : K) • w) ∈ Λ := hφ (hcb' w hw)
    have h2 := Λ.smul_mem u h1
    rw [← algebraMap_smul K u, map_smul, smul_smul] at h2
    convert h2 using 2
    push_cast; ring
  · rw [LinearMap.toMatrix'_mulVec, LinearMap.smul_apply, ← map_smul]
    exact hψ (hcb w hw)
  · have : u * c * c' - 1 = -(v * (N : 𝓞 K)) := by linear_combination huv
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ hNm)
  · rw [← LinearMap.toMatrix'_comp]
    have e : (((u * c' : 𝓞 K) : K) • φ) ∘ₗ ((c : K) • ψ) = ((u * c * c' : 𝓞 K) : K) • LinearMap.id := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, hφψ, smul_smul]
      congr 1; push_cast; ring
    rw [e, map_smul, LinearMap.toMatrix'_id]
    push_cast
    rw [sub_smul, one_smul]

end GlobalTheory.OntoModPf

namespace GlobalTheory.OntoModPf

open NumberField Matrix

theorem ontoModEx : OntoModEx := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have h0 := G.sp.P_is i hi.le
  have h1 := G.sp.P_is (i + 1) hi
  haveI : (G.Λ (.core i)).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h0.sd
  haveI : (G.Λ (.core (i + 1))).IsFullLattice D.host.E := selfDual_isFullLattice _ _ h1.sd
  have e0 : (G.V (.core i)).rank = rankP D i := h0.rank
  have e1 : (G.V (.core (i + 1))).rank = rankP D (i + 1) := h1.rank
  have hle : (G.V (.core i)).rank ≤ (G.V (.core (i + 1))).rank := by
    rw [e0, e1]; unfold rankP; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ i)) _
  obtain ⟨x, hx, y, hy, a, ha, hxy⟩ :=
    exists_onto_mod hle (G.Λ (.core i)) (G.Λ (.core (i + 1))) G.modul (G.pl.modul_ne_bot sc)
  refine ⟨x, hx, y, hy, ?_⟩
  have h1m : (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) ∈
      homLat (G.Λ (.core i)) (G.Λ (.core i)) := fun v hv => by simpa using hv
  have e : x * y - 1 = a • (1 : Matrix (Fin (G.V (.core i)).rank) (Fin (G.V (.core i)).rank) D.host.E) := by
    rw [hxy]; exact algebraMap_smul D.host.E a _
  rw [e]
  exact Submodule.smul_mem_smul ha h1m

end GlobalTheory.OntoModPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomOntoModuloDepthIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeHom_onto_modulo_depthIdeal : OntoModEx := by
  first | exact @GlobalTheory.OntoModPf.ontoModEx | exact GlobalTheory.OntoModPf.ontoModEx | (intros; apply GlobalTheory.OntoModPf.ontoModEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIntertwinerMapValuesIsCuspFun
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueMultMap
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwMult

theorem contRep_facts (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)) (hF : I.IsFundDom (I.muA μf) fund)
    (hR : I.IsRightReg μf fund R) (y : I.L2 μf fund) (f : I.GA → ℂ) (hc : Continuous f)
    (hi : ∀ γ ∈ I.GFset, ∀ x, f (γ * x) = f x) (he : ∀ᵐ x ∂(I.muA μf), f x = I.ext y x) :
    (∀ f' : I.GA → ℂ, Continuous f' → (∀ᵐ x ∂(I.muA μf), f' x = I.ext y x) → f' = f) ∧
    (I.IsCuspFn (I.muA μf) (I.ext y) → I.IsCuspFn (I.muA μf) f) ∧
    ∀ (k : I.GA) (c : ℂ), R k y = c • y → ∀ x, f (x * k) = c * f x := by
  classical
  have hH : I.IsHilbTensor (H := fun _ => ℂ) (fun _ _ => ContinuousLinearMap.id ℂ ℂ)
      (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) := by
    refine ⟨fun x y => ?_, fun _ _ => rfl, ?_⟩
    · simp only [RCLike.inner_apply, map_prod, ← Finset.prod_mul_distrib]
    · have hspan : Submodule.span ℂ (Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v) = ⊤ := by
        refine eq_top_iff.2 fun z _ => ?_
        have h1 : (1 : ℂ) ∈ Set.range fun x : (∀ _ : InfinitePlace I.F, ℂ) => ∏ v, x v :=
          ⟨fun _ => 1, by simp⟩
        simpa using Submodule.smul_mem _ z (Submodule.subset_span h1)
      rw [hspan, Submodule.top_coe]
      exact dense_univ
  let B : RowsAut := GlobalTheory.RepSmooth.bundle I μf fund R (fun _ => ℂ) (fun _ => inferInstance)
    (fun _ _ => ContinuousLinearMap.id ℂ ℂ) ℂ (fun _ => ContinuousLinearMap.id ℂ ℂ) (fun x => ∏ v, x v) hF hR hH 1
  have hy : GlobalTheory.Dec.IsContRep B y f := GlobalTheory.RepSmooth.isContRep_of_ae B hc hi he
  obtain ⟨-, -, htr, hfin⟩ := GlobalTheory.ExtContRep.ext_ae_eq_contRep B y f hy
  obtain ⟨huniq, hlin, -, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  refine ⟨fun f' hc' he' => ?_, fun hcu W hW ν hν => ?_, fun k c hk x => ?_⟩
  · have hae : ∀ᵐ x ∂(I.muA μf), f' x = f x := by
      filter_upwards [he', he] with x h1 h2
      rw [h1, h2]
    exact GlobalTheory.RepSmooth.eq_of_ae B hc' hc hae
  · haveI : IsFiniteMeasure ν := hν.1
    filter_upwards [hcu W hW ν hν, hfin ν inferInstance] with x h1 h2
    have h2' : ∀ᵐ m ∂ν, I.ext y (m * x) = f (m * x) := h2
    rw [← h1]
    exact integral_congr_ae (h2'.mono fun m hm => hm.symm)
  · have h3 : GlobalTheory.Dec.IsContRep B (R k y) (fun x => f (x * k)) := htr k
    rw [hk] at h3
    have h4 := hlin y y f f (c - 1) hy hy
    have e1 : y + (c - 1) • y = c • y := by
      rw [sub_smul, one_smul, add_sub_cancel]
    rw [e1] at h4
    have h5 : f (x * k) = f x + (c - 1) * f x := congrFun (huniq _ _ _ h3 h4) x
    rw [h5]
    ring

end GlobalTheory.IntertwMult
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCuspHomOfCuspLowest
open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult GlobalTheory.RowLev NumberField Matrix
open scoped InnerProductSpace TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLev

theorem isCuspHom_of_cusp_lowest : ∀ (B : RowsAut), (∀ v, IsDS (B.I.ε v) (B.lam v) (B.σ v)) → (∀ v, ‖B.w v‖ = 1) → ∀ A ∈ B.I.eHom B.σs B.μf B.fund B.R B.Re, B.I.IsCuspFn (B.I.muA B.μf) (B.I.ext (A (B.tens B.w))) → IsCuspHom B.I A := by
  intro B hDS hw A hA hcusp
  obtain ⟨S, hS, hSc, hSR, -⟩ := GlobalTheory.CuspSubspace.cuspidal_closed_stable B
  obtain ⟨-, -, -, -, hirr⟩ :=
    GlobalTheory.HilbTensorRep.tensor_rep_rows B fun v => ⟨(hDS v).2.2.1, (hDS v).2.2.2.1⟩
  obtain ⟨T₀, hT₀, rfl⟩ := Submodule.mem_map.mp hA
  have hT₀' : ∀ g : B.I.Ginf, T₀.comp (B.σs g) = (B.R (g, 1)).comp T₀ := hT₀
  have hRe := (GlobalTheory.IdemProj.re_orth_proj B).2.1

  have hint : ∀ (g : B.I.Ginf) (u : B.Hs),
      B.Re (T₀ (B.σs g u)) = B.R (g, 1) (B.Re (T₀ u)) := by
    intro g u
    have h1 := congrArg (fun L => L u) (hT₀' g)
    have h2 := congrArg (fun L => L (T₀ u)) (hRe g)
    simp only [ContinuousLinearMap.comp_apply] at h1 h2
    rw [h1, h2]

  let P : Submodule ℂ B.Hs := S.comap (B.Re.comp T₀ : B.Hs →L[ℂ] B.I.L2 B.μf B.fund).toLinearMap
  have hPc : IsClosed (P : Set B.Hs) :=
    hSc.preimage (B.Re.comp T₀).continuous
  have hPs : ∀ g, ∀ u ∈ P, B.σs g u ∈ P := by
    intro g u hu
    change B.Re (T₀ (B.σs g u)) ∈ S
    rw [hint]
    exact hSR _ _ hu
  have hw0 : B.tens B.w ∈ P := by
    change B.Re (T₀ (B.tens B.w)) ∈ S
    rw [hS]
    simpa [ContinuousLinearMap.compL_apply] using hcusp
  have hne : B.tens B.w ≠ 0 := by
    intro h0
    have hn := GlobalTheory.HilbTensorRep.norm_tens B.tens_spec.1 B.w
    rw [h0, norm_zero] at hn
    simp [hw] at hn
  rcases hirr P hPc hPs with hbot | htop
  · exact absurd ((Submodule.mem_bot ℂ).mp (hbot ▸ hw0)) hne
  · intro u
    have hu : u ∈ P := htop ▸ Submodule.mem_top
    have : B.Re (T₀ u) ∈ S := hu
    simpa [ContinuousLinearMap.compL_apply] using (hS _).mp this

end GlobalTheory.RowLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeOntoCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

end GlobalTheory.SeeOntoCusp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemUnipotentRadicalIffIotaMemAdelicRadicalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) := by
  first | exact @GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | exact GlobalTheory.SeeOntoCusp.mem_NI_iff_iota | (intros; apply GlobalTheory.SeeOntoCusp.mem_NI_iff_iota <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjCusp

theorem isCuspFun_iota (D : D7) (I : AutInst) (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (μf : Measure I.Gf)
    [μf.IsHaarMeasure] [SigmaFinite μf] (ψ : I.GA → ℂ) (hc : Continuous ψ)
    (hi : ∀ γ ∈ I.GFset, ∀ y, ψ (γ * y) = ψ y) (hcusp : I.IsCuspFn (I.muA μf) ψ) :
    IsCuspFun (D.sp.Y 0) (fun g => ψ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) g)) := by
  subst h
  intro r C hC μ 𝓕 hμ h𝓕 g
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range C.col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (Formalism.IndefR.RationalEmbedding.iota_rat D) _ hW (GlobalTheory.T.mem_unipotentRadical_iff_iota_mem_adelicRadical D C hC) ψ hc hi).2 (hcusp _ hW) μ 𝓕 hμ h𝓕 g
  exact key

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, IsCuspFun (Yc D 0) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c ht hConj hInt Φ hΦ hRep u
  change IsCuspFun (D.sp.Y 0) _
  obtain ⟨-, -, -, -, -, -, hSL⟩ := GlobalTheory.ClassificationConsequences.consequences_of_dsClass hDS
  obtain ⟨hd, hl, hb, hh, hph, -⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  have hg : 1 ≤ X.B.g := by
    rw [X.g_eq]; exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  obtain ⟨-, -, ⟨T0, hT0⟩, -⟩ := GlobalTheory.GlobProj.globalProj_holds X.B X.dv hd hph
  have hw := GlobalTheory.RowCusp.row_isCuspFn hSL X.B X.dv _ hd hg hh hl hb T0 hT0 Φ hΦ
  have hcH := GlobalTheory.RowLev.isCuspHom_of_cusp_lowest X.B X.ds (fun v => (X.low v).1) Φ hΦ hw
  obtain ⟨ψ, hψ⟩ := hRep u
  have he := (GlobalTheory.ExtContRep.ext_ae_eq_contRep X.B _ ψ hψ).1
  have hcψ : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ :=
    (GlobalTheory.IntertwMult.contRep_facts X.B.I X.B.μf X.B.fund X.B.R X.B.fund_spec X.B.R_spec _ ψ hψ.1 hψ.2.1
      (he.mono fun x hx => hx.symm)).2.1 (hcH _)
  have hY := isCuspFun_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hcψ
  set t' : GA D (D.sp.Y 0) := t with ht'
  have hfun : GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u = fun y => star (ψ (iotaX X h (y * t'⁻¹))) := by
    funext y
    exact congrArg star (congrFun (GlobalTheory.ConjRowMult.contRepL_spec X hψ) _)
  rw [hfun]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have key := hY r C hC μ 𝓕 hμ h𝓕 (g * t'⁻¹)
  have e : ∀ n : NI (D.sp.Y 0) C, ((n : GA D (D.sp.Y 0)) * g * t'⁻¹) = (n : GA D (D.sp.Y 0)) * (g * t'⁻¹) :=
    fun n => mul_assoc _ _ _
  have hs : ∀ z : ℂ, star z = starRingEnd ℂ z := fun _ => rfl
  simp only [e, hs]
  rw [integral_conj]
  exact (congrArg (starRingEnd ℂ) key).trans (map_zero _)

end GlobalTheory.ConjCusp

end
end
