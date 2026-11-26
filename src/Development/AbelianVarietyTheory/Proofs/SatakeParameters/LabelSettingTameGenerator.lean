module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeCharRealSubfieldAlgebraicOfCompNormIntegral
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.JointCondTBAtRange
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistedStartColumnReading
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LevelGroupNeTopNeBot
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne Formalism.CyclotomicNorms

namespace GlobalTheory.LabLaws

section WDLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
variable {g : ℕ} [Fact g.Prime]

end WDLaws

section Comparison₂

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

def LabTie (T : GlobalTheory.RowTie.WDTie N A) (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ)
    (γ : Fin 2 → PlE H → G H.E N.Om) : Prop :=
  ∀ (k : Fin 2) (v : N.PlG k),
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    IsTeich (τ k) ∧ TameGenAt (N.plOm.1 (A.plGw k v)) (γ k (A.plGw k v)) ∧
      ∀ a : A.LP (A.plGw k v), A.items₂ k (A.plGw k v) a = WD.lab (τ k) (γ k (A.plGw k v)) (T.e _ a)

theorem tieLab_of_labTie {T : GlobalTheory.RowTie.WDTie N A} {τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ}
    {γ : Fin 2 → PlE H → G H.E N.Om} (hT : LabTie T τ γ) : GlobalTheory.RowCopy.TieLab N A := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, (hT k v).2.2, T.tw, WD.lab_lpTw]
  · haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    rw [(hT k v).2.2, ← T.dim]
    exact WD.natDegree_lab_le _ _ _

end Comparison₂

section Inhabited

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

end Inhabited

end GlobalTheory.LabLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedP
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

noncomputable section

namespace GlobalTheory.RegAlgCharAlg

theorem expo_mul' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ χ' : HChar E) (τ : E →+* ℂ) :
    expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv' {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (τ : E →+* ℂ) :
    expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul' χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isAlgPos_of_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ →
      ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  intro E _ _ _ a ha π χ hreg hpol
  refine GlobalTheory.T.heckeChar_realSubfield_algebraic_of_comp_norm_integral E χ fun τ => ?_
  have hcomm : ∀ (τ : E →+* ℂ) (u : ℂ) (o : Op E a), Commute (cap (a := a) τ u) (act o) := fun τ u o => by
    cases o with
    | fin k => exact commute_cap_finRep τ u k
    | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
    | lie X => exact commute_cap_lie τ u X
  have hm : ∀ σ, π.HasInfChar σ ((CG.mk π).infChar σ) := fun σ =>
    GlobalTheory.CuspRep.hasInfChar_infChar_of_commute E a hcomm (CG.mk π) σ
  set ψ := GlobalTheory.GalOfCusp.compNorm E χ
  have h1 := (hm τ).twist ψ⁻¹
  have key := GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing E a (π.twist ψ⁻¹) π hpol.dual τ _ _ h1 (hm (NumberField.ComplexEmbedding.conjugate τ))
  obtain ⟨z, hz⟩ : ∃ z, z ∈ (CG.mk π).infChar τ :=
    Multiset.card_pos_iff_exists_mem.1 (by rw [(hm τ).1]; omega)
  obtain ⟨n, hn⟩ := (hreg τ).2 z hz
  have hz' : -(z + expo ψ⁻¹ τ) ∈ (CG.mk π).infChar (NumberField.ComplexEmbedding.conjugate τ) := by
    rw [key, Multiset.map_map]
    exact Multiset.mem_map.2 ⟨z, hz, rfl⟩
  obtain ⟨n', hn'⟩ := (hreg _).2 _ hz'
  refine ⟨n + n' + ((a : ℤ) - 1), ?_⟩
  rw [expo_inv'] at hn'
  push_cast
  linear_combination hn' + hn

end GlobalTheory.RegAlgCharAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfRegularAlgebraicPolarizedPStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraicHeckeChar_of_regularAlgebraic_polarizedPair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → PolarizedPair π χ → ∃ n : (maximalRealSubfield E →+* ℂ) → ℤ, IsAlgPos χ n := by
  first | exact @GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair | exact GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair | (intros; apply GlobalTheory.RegAlgCharAlg.isAlgPos_of_polarizedPair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff
section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AssocSetApplyOfPointwise
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

structure RActPre (X : Scheme.{0}) (Γ : Type) [Group Γ] where

  P : (Over X)ᵒᵖ ⥤ Type

  act : Γ → (P ⟶ P)
  act_one : act 1 = 𝟙 P
  act_mul : ∀ g h, act (g * h) = act g ≫ act h

variable {X : Scheme.{0}} (E : Type) [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable {E} (Q : RActPre X Γ) (ξ : Γ →* GL ι E)

end

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

end GlobalTheory.Et.Rel
end
end

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]

section
variable (f : X ⟶ Y)

end

variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.Et.Rel

variable {X Y : Scheme.{0}} {E : Type} [CommRing E] [TopologicalSpace E] [IsTopologicalRing E]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ]
variable (E) (f : X ⟶ Y) (Q' : RActPre X Γ) (Q : RActPre Y Γ) (ξ : Γ →* GL ι E)
  (e : ∀ T : Over X, Q'.P.obj (op T) ≃ Q.P.obj (op ((Over.map f).obj T)))
  (he : ∀ {T₁ T₂ : Over X} (v : T₁ ⟶ T₂) (η : Q'.P.obj (op T₂)),
    e T₁ (Q'.P.map v.op η) = Q.P.map ((Over.map f).map v).op (e T₂ η))
  (hq : ∀ (T : Over X) (γ : Γ) (η : Q'.P.obj (op T)), e T ((Q'.act γ).app (op T) η) = (Q.act γ).app _ (e T η))

end GlobalTheory.Et.Rel

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

def ObjMap.ptEquiv (m : ObjMap o' o f) (T : Over S') : (T ⟶ o'.A) ≃* ((Over.map f).obj T ⟶ o.A) :=
  MulEquiv.ofBijective (pushHom m.cart T) ⟨GlobalTheory.SiegelPull.push_injective m.cart T, GlobalTheory.SiegelPull.push_surjective m.cart T⟩

theorem ObjMap.ptEquiv_left (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) :
    (m.ptEquiv T x).left = x.left ≫ m.φ := rfl

theorem ObjMap.ptEquiv_act (m : ObjMap o' o f) (T : Over S') (x : T ⟶ o'.A) (c : D.O) :
    m.ptEquiv T (x ≫ o'.act.act c) = m.ptEquiv T x ≫ o.act.act c :=
  Over.OverMorphism.ext (by
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, m.act,
      Category.assoc])

theorem ObjMap.exists_ptEquiv (m : ObjMap o' o f) (Z : Over S) (g : Z.left ⟶ S') (hg : g ≫ f = Z.hom) :
    ∃ σ : (Over.mk g ⟶ o'.A) ≃* (Z ⟶ o.A), (∀ x, (σ x).left = x.left ≫ m.φ) ∧
      ∀ (n : ℤ) (a c : Over.mk g ⟶ o'.A) (z : Γ(Z.left, ⊤)ˣ),
        (Out.WeilIs o'.A (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) n a c z ↔
          Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n (σ a) (σ c) z) := by
  obtain ⟨Zl, Zr, Zh⟩ := Z
  change Zl ⟶ S' at g
  change g ≫ f = Zh at hg
  subst hg
  refine ⟨m.ptEquiv (Over.mk g), fun x => rfl, fun n a c z => ?_⟩
  exact GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ o.A o'.A f m.φ _ _ (pull_isLB o.isLB _) (pull_isLB o'.isLB _)
    m.cart (GlobalTheory.SiegelPull.diag_iso m.sq m.pol) (Over.mk g) n a c _ _ z rfl rfl

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

open CategoryTheory Limits AlgebraicGeometry Opposite Matrix MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s} {f : S' ⟶ S}

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbedding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.DatumJets.Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 :=
  GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    nlinarith [hcon.1, hcon.2]

theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ ι : K →+* ℂ_[p], w.asIdeal = smallIdeal ι := by
  by_contra hcon
  push Not at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p]) := by
    intro σ hle
    exact hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])),
        (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p]) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]

theorem valuation_le_one_of_norm (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : ‖ι x‖ ≤ 1) :
    w.valuation K x ≤ 1 := by
  by_contra hcon
  have hgt : 1 < w.valuation K x := not_le.1 hcon
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt
  have hinv : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have hn : n ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← h, map_mul]
    calc w.valuation K x⁻¹ * w.valuation K (algebraMap (𝓞 K) K d) ≤ w.valuation K x⁻¹ * 1 :=
          mul_le_mul_right (w.valuation_le_one _) _
      _ < 1 := by rwa [mul_one]
  have hn' := (hw n).1 hn
  have h2 : ((d : 𝓞 K) : K) = x * (n : K) := by
    have h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K) := h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [h2, map_mul, norm_mul] at hd
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (n : K))]

theorem placeAbove : GlobalTheory.DatumJets.PlaceAbove := by
  intro K _ _ σ p _ w hw
  obtain ⟨ι, hι⟩ := exists_embedding w hw
  have hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1 := fun y => by rw [hι]; rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.MomPlace.exists_extension K p σ ι
  refine ⟨lam, fun k => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt
  rw [(hlam k).2]
  exact ⟨fun h => valuation_le_one_of_norm ι w hw' k h.2,
    fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩

end GlobalTheory.DatumJets.Place
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceOverPInducedByAlgebraicPadicEmbeddingStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_over_p_induced_by_algebraic_padic_embedding : GlobalTheory.DatumJets.PlaceAbove := by
  first | exact @GlobalTheory.DatumJets.Place.placeAbove | exact GlobalTheory.DatumJets.Place.placeAbove | (intros; apply GlobalTheory.DatumJets.Place.placeAbove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section Gen

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {n r b : ℕ}

theorem parL_map_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) {v : Sp E n} (hv : v ∈ LocE.parL P (qOf P) r n 0) :
    j.1 v ∈ LocE.parL P (qOf P) r n 0 := by
  have hq0 := qOf_ne_zero (P := P)
  have hv' : ∀ l : Fin n, IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * v l) :=
    GlobalTheory.LastSteps.mem_sclLat.1 hv
  have hv0 : ∀ l : Fin n, IntAt P (v l) := fun l => by
    have h1 := hv' l
    split_ifs at h1
    · have h2 := (intAt_nat (P := P) (qOf P)).mul h1
      rwa [zpow_one, mul_inv_cancel_left₀ hq0] at h2
    · simpa using h1
  refine GlobalTheory.LastSteps.mem_sclLat.2 fun (l : Fin n) => ?_
  show IntAt P (((qOf P : E) ^ (if r ≤ l.1 ∧ l.1 < n then (1 : ℤ) else 0))⁻¹ * j.1 v l)
  split_ifs with hl
  · have e := apply_eq_sum (j.1 : Sp E n →ₗ[E] Sp E n) v l
    rw [LinearEquiv.coe_coe] at e
    rw [e, Finset.mul_sum, zpow_one]
    refine intAt_sum _ fun i _ => ?_
    by_cases hi : r ≤ i.1
    · have h1 := hv' i
      rw [if_pos ⟨hi, i.2⟩, zpow_one] at h1
      rw [← mul_assoc]
      exact h1.mul (glint_entry j l i)
    · have h0 : redP P (j.1 (Pi.single i 1) l) = 0 :=
        mem_btG.1 h l i (by rw [coarse_of_lt (Nat.not_le.1 hi), coarse_of_le hl.1]; omega)
      have h1 := (hv0 i).mul (intAt_div_of_redP hq (glint_entry j l i) h0)
      convert h1 using 1
      ring
  · rw [zpow_zero, inv_one, one_mul]
    exact mem_stdAt.1 (glint_mem j (mem_stdAt.2 hv0)) l

theorem mem_JQ_of_red (hq : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) : j.1 ∈ LocE.JQ P (qOf P) r n 0 := by
  refine ⟨j.2, fun v => ⟨fun hv => ?_, parL_map_of_red hq j h⟩⟩
  have h1 := parL_map_of_red hq j⁻¹ (by rw [map_inv]; exact inv_mem h) hv
  have e : (j⁻¹).1 (j.1 v) = v := LinearEquiv.symm_apply_apply j.1 v
  exact e ▸ h1

theorem lamQB_eq_red (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (hn : n = r + b) (j : GLint E n P)
    (h : redGL n P j ∈ HQ (𝓞 E ⧸ P.asIdeal) n r b) :
    LocE.lamQB ξ r n j.1.toLinearMap = (((lamQ ξ n r b ⟨_, h⟩)⁻¹ : Kˣ) : K) := by
  have hA : GlobalTheory.DatumLaw.IntM P n n fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p := fun p p' hp hp' => by
    show IntAt P (Loc.atN _ _)
    rw [GlobalTheory.LastSteps.eN_eq hp', Loc.atN, dite_eq_left hp]
    exact glint_entry j _ _
  have h1 := blkDet_eq_dB (coarse r [b]) 1 r (n - r) (by omega) (fun i hi => by
    by_cases hr : i < r
    · rw [coarse_of_lt hr]; omega
    · rw [coarse_of_le (Nat.not_lt.1 hr), blkIdx, if_pos (by omega)]; omega) ⟨_, h⟩
    (GlobalTheory.DatumLaw.red P fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) (fun i l => by
      show redP P (Loc.atN _ _) = _
      rw [GlobalTheory.LastSteps.eN_eq l.2, Loc.atN, dite_eq_left i.2]
      rfl)
  rw [← GlobalTheory.DatumLaw.redP_dB hA (by omega) (by omega)] at h1
  rw [lamQ_apply, Units.val_inv_eq_inv_val]
  show (GlobalTheory.DatumLaw.ext0 ξ (redP P (GlobalTheory.DatumLaw.dB (fun p p' => Loc.atN (j.1.toLinearMap (Loc.eN E n p')) p) r (n - r))))⁻¹ = _
  rw [← h1, GlobalTheory.DatumLaw.ext0, dite_eq_left (Units.isUnit _), IsUnit.unit_of_val_units]

end Gen

theorem phiTop_target_twist : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (m2 : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), R.m = m2 + 2 → ((qOf P : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 → P ∉ Pr.vGs → ∀ (sharp : Bool) (Q : Finset (HeightOneSpectrum (𝓞 X.E))) (hQ : P ∈ Q) (j : GLint X.E (R.N R.m - 1) P) (h : redGL _ P j ∈ (rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).H) (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) (R.N R.m - 1)), PhiTop Ch mu sharp m2 P (j.1.toLinearMap ∘ₗ x) * LocE.unitV (resChar (mu : Chr X.F X.E X.K) P)⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = (((rowTyQ R (mu : Chr X.F X.E X.K) Q ⟨P, hQ⟩).lam ⟨_, h⟩ : X.Kˣ) : X.K) * PhiTop Ch mu sharp m2 P x := by
  intro X Pr R Ch S mu m2 P hm hq hP sharp Q hQ j h x
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.DatumLaw.ranks R (j := m2 + 1) (by omega)
  unfold PhiTop
  rw [if_neg hP]
  have h1 := GlobalTheory.DatumLaw.phiQ_target (resChar (mu : Chr X.F X.E X.K) P) (k₀ := R.k) (r := R.r) (c' := cOf R (m2 + 1))
    (n' := R.N (m2 + 1)) (c := 0) (n := R.N R.m - 1) (kj := R.r) (by omega) (r_le_X' R) rfl (by omega)
    (mem_JQ_of_red hq j h) x
  exact h1.trans (congrArg (· * _) (lamQB_eq_red _ (rank_X'_eq R) j h))

end GlobalTheory.TopLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtOneOfContinuous
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Filter Topology Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneLift

section Val

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M]

theorem tendsto_pow {v : HeightOneSpectrum (𝓞 K)} (x : v.adicCompletion K) (h : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ h (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' h.le hm) hn

theorem lt_one_of_continuous {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (s : v.adicCompletion K →+* w.adicCompletion M) (hs : Continuous s) {z : v.adicCompletion K}
    (hz : Valued.v z < 1) : Valued.v (s z) < 1 := by
  have h1 : Tendsto (fun n : ℕ => s z ^ n) atTop (𝓝 0) := by
    have := (hs.tendsto 0).comp (tendsto_pow z hz)
    simpa [Function.comp_def, map_pow] using this
  have hU : {y : w.adicCompletion M | Valued.v y < 1} ∈ 𝓝 (0 : w.adicCompletion M) :=
    Valued.mem_nhds_zero.2 ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨N, hN⟩ := (h1.eventually hU).exists
  by_contra hc
  rw [not_lt] at hc
  have hN' : Valued.v (s z ^ N) < 1 := hN
  rw [map_pow] at hN'
  exact absurd hN' (not_lt.2 (one_le_pow₀ hc))

theorem mem_iff_lt_one (v : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ v.asIdeal ↔ Valued.v (algebraMap K (v.adicCompletion K) (x : K)) < 1 := by
  have h : Valued.v (algebraMap K (v.adicCompletion K) (x : K)) = v.valuation K (algebraMap (𝓞 K) K x) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  rw [h, HeightOneSpectrum.valuation_lt_one_iff_mem]

theorem over_of_continuous (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)}
    (i : v.adicCompletion K →+* w.adicCompletion M) (hi : Continuous i)
    (he : ∀ x : K, i (algebraMap K _ x) = algebraMap M _ (e x)) : Over e v w := by
  have h1 : v.asIdeal ≤ (src e w).asIdeal := by
    intro x hx
    rw [ringEquivPlaceCorrespondence_placeUnder e w x, mem_iff_lt_one]
    rw [mem_iff_lt_one] at hx
    have := lt_one_of_continuous i hi hx
    rw [he] at this
    exact this
  have h2 : v = src e w := HeightOneSpectrum.ext (v.isMaximal.eq_of_le (src e w).isPrime.ne_top h1)
  rw [h2]
  exact ringEquivPlaceCorrespondence_placeUnder e w

theorem normV_eq_absNorm (v : HeightOneSpectrum (𝓞 K)) : normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem two_le_normV (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  rw [normV_eq_absNorm]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

end Val

end GlobalTheory.DegOneLift

namespace GlobalTheory.DegOneLift

section Rep

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  {a : ℕ}

theorem pull_pull (e : K ≃+* M) (φ : Sm K a) : pull a e (pull a e.symm φ) = φ :=
  Subtype.ext <| funext fun g => congrArg φ.1 (mapA_symm e g)

theorem pullSub_pullSub (e : K ≃+* M) (π : CuspSub K a) : pullSub e (pullSub e.symm π) = π := by
  refine CuspSub.ext ?_
  change (π.V.map (pull a e.symm).toLinearMap).map (pull a e).toLinearMap = π.V
  rw [← Submodule.map_comp]
  convert Submodule.map_id π.V
  refine LinearMap.ext fun φ => ?_
  exact pull_pull e φ

def SmIrr.comap {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H] (σ : SmIrr H)
    (f : G →* H) (hf : Continuous f) (hs : Function.Surjective f) : SmIrr G where
  V := σ.V
  ρ := σ.ρ.comp f
  smooth x := (σ.smooth x).preimage hf
  irred := by
    obtain ⟨h0, h⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 σ.irred
    refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h W fun g x hx => ?_⟩
    obtain ⟨g, rfl⟩ := hs g
    exact hW g x hx

theorem locRep_pullSub (e : K ≃+* M) {v : HeightOneSpectrum (𝓞 K)} {w : HeightOneSpectrum (𝓞 M)} (hO : Over e v w)
    (π : CuspSub K a) (g : GL (Fin a) (v.adicCompletion K)) (x : π.V) :
    (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) ((pull a e.symm).submoduleMap π.V x) =
      (pull a e.symm).submoduleMap π.V (π.locRep v g x) := by
  apply Subtype.ext
  refine Eq.trans ?_ (pull_act e.symm (.fin (locGL K a v g)) x.1).symm
  change _ = act (.fin (GeneralLinearGroup.map (cFin e) (locGL K a v g))) (pull a e.symm x.1)
  rw [cFin_locGL hO]
  rfl

end Rep

theorem isLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ) (π : CuspSub K a), ∃ P : CuspSub M a, GlobalTheory.GalCut.IsLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a π
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  refine ⟨pullSub e.symm π, ?_, ?_, ?_⟩
  · intro w f B hf hB
    have hO : Over e.symm w (w.under (𝓞 K)) := fun x => by
      rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap]
      have : algebraMap (𝓞 K) (𝓞 M) (RingOfIntegers.mapRingEquiv e.symm x) = x := by
        apply RingOfIntegers.ext
        change algebraMap K M (e.symm (x : M)) = x
        rw [← he]
        exact e.apply_symm_apply _
      rw [this]
    have hq : normV w = normV (w.under (𝓞 K)) := by
      rw [normV_eq_absNorm, normV_eq_absNorm]
      exact (qV_eq hO).symm
    have h2 := two_le_normV (w.under (𝓞 K))
    have hf1 : f = 1 := Nat.pow_right_injective h2 (by
      change normV (w.under (𝓞 K)) ^ f = normV (w.under (𝓞 K)) ^ 1
      rw [pow_one, ← hf, hq])
    subst hf1
    simp only [pow_one, Multiset.map_id']
    exact hasSat_pullSub e.symm hO hB
  · intro τ
    have hτ : (τ.comp e.toRingHom).comp e.symm.toRingHom = τ := by
      ext x
      simp
    have key : ∀ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m ↔
        (CG.mk (pullSub e.symm π)).HasInfChar τ m := by
      intro m
      constructor
      · intro h
        exact hasInfChar_pullSub e.symm (π := π) (σ := τ) h
      · intro h
        have h3 : (pullSub e (pullSub e.symm π)).HasInfChar (τ.comp e.toRingHom) m :=
          hasInfChar_pullSub e (σ := τ.comp e.toRingHom) (by rw [hτ]; exact h)
        rw [pullSub_pullSub] at h3
        exact h3
    by_cases h : ∃ m, (CG.mk π).HasInfChar (τ.comp (algebraMap K M)) m
    · obtain ⟨m, hm⟩ := h
      rw [((key m).1 hm).infChar_eq, hm.infChar_eq]
    · have h' : ¬ ∃ m, (CG.mk (pullSub e.symm π)).HasInfChar τ m := fun ⟨m, hm⟩ => h ⟨m, (key m).2 hm⟩
      unfold CG.infChar
      rw [dite_eq_right h, dite_eq_right h']
  · intro v w i hi hie σ σ' hσ hσ'
    have hO : Over e v w := over_of_continuous e i.toRingHom hi fun x => hie x
    have hiL : ∀ y, i y = cLoc hO y := fun y => congrFun
      ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer hi (continuous_cLoc hO)
        (funext fun x => (hie x).trans (cLoc_algebraMap hO x).symm)) y
    have hsurj : Function.Surjective (GeneralLinearGroup.map (n := Fin a) (cLoc hO)) := fun g =>
      ⟨GeneralLinearGroup.map (locEquiv hO).symm.toRingHom g, Units.ext (Matrix.ext fun _ _ =>
        (locEquiv hO).apply_symm_apply _)⟩
    let σ'' := SmIrr.comap σ' (GeneralLinearGroup.map (n := Fin a) (cLoc hO))
      (continuous_mapGL _ (continuous_cLoc hO)) hsurj
    let T := (pull a e.symm).submoduleMap π.V
    have h'' : π.IsLocComp v σ'' := by
      obtain ⟨f, h0, hf⟩ := hσ'
      refine ⟨T.symm.toLinearMap ∘ₗ f, fun hz => h0 (LinearMap.ext fun x => T.symm.injective ?_), fun g x => ?_⟩
      · exact (LinearMap.congr_fun hz x).trans (map_zero T.symm).symm
      · have e1 := hf (GeneralLinearGroup.map (cLoc hO) g) x
        have e2 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (T (T.symm (f x))) =
            T (π.locRep v g (T.symm (f x))) := locRep_pullSub e hO π g (T.symm (f x))
        have e3 : (pullSub e.symm π).locRep w (GeneralLinearGroup.map (cLoc hO) g) (f x) =
            T (π.locRep v g (T.symm (f x))) := by
          refine Eq.trans ?_ e2
          exact congrArg _ (T.apply_symm_apply (f x)).symm
        exact (congrArg T.symm (e1.trans e3)).trans (T.symm_apply_apply _)
    obtain ⟨E⟩ := GlobalTheory.CuspRep.LocUniq.isLocComp_unique π v σ σ'' hσ h''
    refine ⟨E.toLinearEquiv, fun g x => ?_⟩
    have hg : GeneralLinearGroup.map i.toRingHom g = GeneralLinearGroup.map (cLoc hO) g :=
      Units.ext (Matrix.ext fun _ _ => hiL _)
    rw [hg]
    exact LinearMap.congr_fun (E.isIntertwining' g) x

end GlobalTheory.DegOneLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntAtFormOfMemStdAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.TopStep

namespace GlobalTheory.TopLaw

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}

theorem intAt_form_of_mem_stdAt (a : E) (η : Sp E n →ₗ[E] E) (h : ∀ i, IntAt P (a * η (Pi.single i 1))) {v : Sp E n}
    (hv : v ∈ stdAt E n P) : IntAt P (a * η v) := by
  rw [GlobalTheory.TopInv.form_apply η v, Finset.mul_sum]
  refine GlobalTheory.TopStep.intAt_sum _ fun j _ => ?_
  rw [mul_left_comm]
  exact (mem_stdAt.1 hv j).mul (h j)

theorem intAt_form_comp_iff (a : E) (κ : GLint E n P) (η : Sp E n →ₗ[E] E) :
    (∀ i, IntAt P (a * (η ∘ₗ κ.1.toLinearMap) (Pi.single i 1))) ↔ ∀ i, IntAt P (a * η (Pi.single i 1)) := by
  refine ⟨fun h i => ?_, fun h i => intAt_form_of_mem_stdAt a η h (glint_mem κ (single_mem_stdAt i))⟩
  have h1 := intAt_form_of_mem_stdAt a _ h (glint_mem κ⁻¹ (single_mem_stdAt i))
  have e : κ.1 ((κ⁻¹).1 (Pi.single i 1)) = Pi.single i 1 := LinearEquiv.apply_symm_apply κ.1 _
  have e' : (η ∘ₗ κ.1.toLinearMap) ((κ⁻¹).1 (Pi.single i 1)) = η (Pi.single i 1) := congrArg η e
  rwa [e'] at h1

end SlopeTestRemainingChoices

theorem psi_add_int {X : Fields} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} {c : LocCst X SB} (hc : c.Ok) (P : SB) {k : ℕ}
    (hk : k ≤ c.D P) {x z : X.E} (hx : IntAt P.1 ((qOf P.1 : X.E) ^ k * x)) (hz : IntAt P.1 (z - x)) :
    c.psi P ((epsSg : X.E) * z) = c.psi P ((epsSg : X.E) * x) := by
  have he : IntAt P.1 ((epsSg : ℤ) : X.E) := intCast_mem (intRing P.1) _
  have hq := fun m => intAt_pow (GlobalTheory.TopStep.intAt_nat (P := P.1) (qOf P.1)) m
  have hd := he.mul hz
  have h1 : IntAt P.1 ((qOf P.1 : X.E) ^ c.D P * ((epsSg : X.E) * x)) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    have := (hq d).mul (he.mul hx)
    convert this using 1
    rw [hd, pow_add]
    ring
  have := hc.psi_add P _ _ h1 ((hq _).mul hd)
  rw [hc.psi_int P _ hd, mul_one] at this
  rw [← this]
  congr 1
  ring

theorem ftY_comp_glint : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)), cst.Ok → ∀ (P : rowSG Pr sel mu), (P.1 ∉ Pr.vGs → 2 * cst.M ≤ cst.D P) → ∀ {n : ℕ} (κ : GLint X.E n P.1) (η : Sp X.E n →ₗ[X.E] X.E) (y' y'' : Sp X.E n), (P.1 ∈ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → (P.1 ∉ Pr.vGs → ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * y' i)) → (P.1 ∈ Pr.vGs → κ.1 y'' - y' ∈ stdAt X.E n P.1) → (P.1 ∉ Pr.vGs → ((qOf P.1 : X.E) ^ cst.M)⁻¹ • (κ.1 y'' - y') ∈ stdAt X.E n P.1) → ftY sel mu cst P (η ∘ₗ κ.1.toLinearMap) y'' = ftY sel mu cst P η y' := by
  intro X Pr sel S mu cst hc P hD n κ η y' y'' hy1 hy2 hk1 hk2
  have hq := qOf_ne_zero (P := P.1)
  unfold ftY
  by_cases hP : P.1 ∈ Pr.vGs
  · rw [if_pos hP, if_pos hP]
    have hi := intAt_form_comp_iff 1 κ η
    simp only [one_mul] at hi
    by_cases h : ∀ i, IntAt P.1 (η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      have h' : ∀ i, IntAt P.1 (1 * η (Pi.single i 1)) := fun i => by rw [one_mul]; exact h i
      refine psi_add_int hc P (hc.D_pos P) ?_ ?_
      · have := intAt_form_of_mem_stdAt 1 η h' (v := (qOf P.1 : X.E) • y') (mem_stdAt.2 (hy1 hP))
        rwa [one_mul, map_smul, smul_eq_mul, ← pow_one (qOf P.1 : X.E)] at this
      · have := intAt_form_of_mem_stdAt 1 η h' (hk1 hP)
        rwa [one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]
  · rw [if_neg hP, if_neg hP]
    have hi := intAt_form_comp_iff ((qOf P.1 : X.E) ^ cst.M) κ η
    by_cases h : ∀ i, IntAt P.1 ((qOf P.1 : X.E) ^ cst.M * η (Pi.single i 1))
    · rw [if_pos h, if_pos (hi.2 h)]
      refine congrArg _ (psi_add_int hc P (hD hP) ?_ ?_)
      · have := intAt_form_of_mem_stdAt _ η h (v := (qOf P.1 : X.E) ^ cst.M • y') (mem_stdAt.2 (hy2 hP))
        rwa [map_smul, smul_eq_mul, ← mul_assoc, ← pow_add, ← two_mul] at this
      · have := intAt_form_of_mem_stdAt _ η h (hk2 hP)
        rwa [map_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hq), one_mul, map_sub] at this
    · rw [if_neg h, if_neg fun h' => h (hi.1 h')]

end GlobalTheory.TopLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvalueCoprimeConjugation
noncomputable section

namespace GlobalTheory.Proof.EigenvalueCoprimeConjugation

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual Formalism.CyclotomicNorms ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.WeilDeligne

variable (D : D7)

theorem normV_plGw (k : Fin 2) (v : D.nd.PlG k) : normV (D.naut.plGw k v) = D.host.g k :=
  normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) (D.naut.plGw_over k v)

end GlobalTheory.Proof.EigenvalueCoprimeConjugation

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePair
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePair
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

namespace GlobalTheory.BadNoConj

theorem sall_noConj_ok : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr sel S mu hX hPr hsel u hT hg
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto
  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'

end GlobalTheory.BadNoConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberBadPrimesNoConjugatePairStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberBadPrimes_no_conjugatePair : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  first | exact @GlobalTheory.BadNoConj.sall_noConj_ok | exact GlobalTheory.BadNoConj.sall_noConj_ok | (intros; apply GlobalTheory.BadNoConj.sall_noConj_ok <;> assumption)
end
end
