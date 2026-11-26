module

public import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.FrameRingGlRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExpFourClauses
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct

namespace GlobalTheory.ExpClauses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
  (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))

theorem expUniq : ExpUniq e F := by
  intro i P P' hP hP' gam h hEF hM hA hrel z
  have hm : ∀ z, Matrix.mulVec (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) z = h z :=
    fun z => LinearMap.toMatrix'_mulVec _ z
  have key := @GlobalTheory.FamRigid.ex_eq_of_level_group GlobalTheory.latMinkowski E _ _ _ H Dw l Xo _ g _ F i P P' gam
    (LinearMap.toMatrix' (h : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))) hP hP' hEF hM hA (fun a => by rw [hm]; exact hrel a)
  have := key.2.2 z
  rwa [hm] at this

theorem expLin : ExpLin e F := by
  intro i P hP m w vs cf v hvs hv
  exact (@GlobalTheory.DerLin.isCombAt_iff_isDerivAt0 E _ _ _ H Dw l Xo _ g _ F i P hP m vs w hvs cf v).2 hv

theorem expTan : ExpTan e F := by
  intro i P hP w v hv
  refine ⟨(@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).1 w v hv, fun j hj => ?_⟩
  refine (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v (e j).1 hv).2 fun j' hj' => ?_
  by_cases hjj : j' = j
  · rw [hjj]
  · exact absurd (by rw [hj, Pi.single_eq_of_ne hjj]) hj'

theorem lieEig : LieEig e F := by
  intro i P hP τ v hv he
  obtain ⟨w, hw, -⟩ := (@GlobalTheory.isDerivAt0_ex_isTanAt E _ _ _ H Dw l Xo _ g _ F i P hP).2.2 v hv
  have hs := (@GlobalTheory.isEigAt_iff_of_isDerivAt0 E _ _ _ H Dw l Xo c σ g e F i P hP w v τ hw).1 he
  refine ⟨fun j => w (e.symm ⟨τ, j⟩), ?_⟩
  have hsum : (∑ j, w (e.symm ⟨τ, j⟩) • eb e τ j) = w := by
    funext k
    obtain ⟨⟨τ', m⟩, rfl⟩ := e.symm.surjective k
    by_cases hτ : τ' = τ
    · subst hτ
      exact sum_eb_apply e τ' (fun j => w (e.symm ⟨τ', j⟩)) m
    · have h0 : w (e.symm ⟨τ', m⟩) = 0 := by
        by_contra hne
        have := hs _ hne
        rw [Equiv.apply_symm_apply] at this
        exact hτ this
      rw [h0]
      simp [Finset.sum_apply, eb_apply, Sigma.mk.inj_iff, hτ]
  rw [hsum]
  exact hw

end GlobalTheory.ExpClauses

theorem GlobalTheory.exp_four_clauses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)), ExpUniq e F ∧ ExpLin e F ∧ ExpTan e F ∧ LieEig e F :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ e F =>
    ⟨GlobalTheory.ExpClauses.expUniq e F, GlobalTheory.ExpClauses.expLin e F, GlobalTheory.ExpClauses.expTan e F, GlobalTheory.ExpClauses.lieEig e F⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStable
noncomputable section

namespace GlobalTheory.Member

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem markMove_finVec_mem {D : D7} (V : HSp D) (g : GA D V) {v : Fin V.rank → D.host.E} (hv : v ∈ latG V g) :
    finVec V v ∈ latGHat V g := by
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.2.1]
  exact AddSubgroup.subset_closure ⟨1, fun w => one_mem _, v, hv, rfl⟩

theorem markMove_mulVec_mem {D : D7} (V : HSp D) (g : GA D V)
    {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ latGHat V 1) :
    (finHom V g).1 *ᵥ y ∈ latGHat V g := by
  have h := (GlobalTheory.Member.latG_lattice_and_completion D V g).2.2.2.1
  rw [(GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1] at hy
  rw [← SetLike.mem_coe, h]
  exact ⟨y, hy, rfl⟩

theorem markMove_finVec_add_nsmul {D : D7} (V : HSp D) (x y : Fin V.rank → D.host.E) (n : ℕ) :
    finVec V (x + n • y) = finVec V x + n • finVec V y := by
  funext i
  simp only [finVec, Pi.add_apply, Pi.smul_apply, TensorProduct.tmul_add]
  congr 1
  exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) n (y i)

theorem markMove_mulVec_nsmul {R : Type} [CommRing R] {m : ℕ} (A : Matrix (Fin m) (Fin m) R) (n : ℕ)
    (y : Fin m → R) : A *ᵥ (n • y) = n • (A *ᵥ y) := Matrix.mulVec_smul _ _ _

theorem markMove_finHom_mul {D : D7} (V : HSp D) (g h : GA D V)
    (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ y = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ y) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]


set_option maxHeartbeats 800000 in
theorem mark_move : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k γ, C.Mark h k γ → (∀ γ₀ ∈ GQ V, C.Mark (γ₀ * h) k (γ * γ₀⁻¹)) ∧ (∀ u, FinCong V l.M u → C.Mark (h * u) k γ) ∧ (∀ u ∈ GinfC V, C.Mark (h * u) k γ) ∧ ∀ δ ∈ (C.M.X k).Γ, ∃ γ₁ ∈ GQ V, C.Mark h k (γ₁ * γ) ∧ C.fr (γ₁ * γ * h) k = lact δ (C.fr (γ * h) k) := by
  intro D H Dw l Xo c σ V r C hC h k γ hM
  obtain ⟨hγ, hΛ, hmk⟩ := hM
  refine ⟨fun γ₀ hγ₀ => ?_, fun u hu => ?_, fun u hu => ?_, fun δ hδ => ?_⟩
  · have e : γ * γ₀⁻¹ * (γ₀ * h) = γ * h := by group
    refine ⟨mul_mem hγ (inv_mem hγ₀), ?_, ?_⟩
    · rw [e]; exact hΛ
    · rw [e]; exact hmk
  · have e : γ * (h * u) = γ * h * u := (mul_assoc _ _ _).symm
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.2.1 l.M (γ * h) u hu
    refine ⟨hγ, ?_, ?_⟩
    · rw [e, e1]; exact hΛ
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hιa : C.ι a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • latG V 1 := by
        rw [← hC.iota.emb.2, ← Submodule.map_top, ← Submodule.map_smul'']
        exact Submodule.mem_map_of_mem ha
      obtain ⟨y, hy, hy'⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V u).2 l.M _).1 (((GlobalTheory.Member.finCong_iff_half_and_kfHalf D H l V).1 u).1 hu) _ hιa
      rw [e, e2]
      refine ⟨w - (finHom V (γ * h)).1 *ᵥ y, sub_mem hw (markMove_mulVec_mem V _ hy), ?_⟩
      rw [markMove_finHom_mul, sub_eq_iff_eq_add'.1 hy', Matrix.mulVec_add, markMove_mulVec_nsmul, nsmul_sub, ← hw',
        sub_add_eq_sub_sub]
  · have e : finHom V (γ * (h * u)) = finHom V (γ * h) := by
      have hu' : finHom V u = 1 := hu
      rw [← mul_assoc, map_mul _ _ u, hu', mul_one]
    obtain ⟨e1, e2⟩ := (GlobalTheory.Member.latG_move D V).2.1 _ _ e
    refine ⟨hγ, ?_, ?_⟩
    · rw [e1]; exact hΛ
    · rw [e2, e]; exact hmk
  · have hr := C.hr
    subst hr
    obtain ⟨⟨hU, hS⟩, hcong, -⟩ := (hC.base.gam k δ).1 hδ
    have hG : (C.M.X k).Gm = -V.gramᵀ := (hC.modelW k).1
    rw [hG] at hU
    obtain ⟨r1, -, r3, -, r5⟩ := GlobalTheory.Member.RatElt.rational_elements D V
    obtain ⟨γ₁, hγ₁⟩ := r3 δ hU
    have hq : γ₁ ∈ GQ V := (r1 γ₁).2 ⟨δ, hγ₁⟩
    obtain ⟨m1, m2⟩ := (GlobalTheory.Member.latG_move D V).1 γ₁ δ (γ * h) hγ₁
    obtain ⟨f1, f2⟩ := r5 γ₁ δ hγ₁
    have hΛ' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ * h) := fun v => by
      rw [← SetLike.mem_coe, hΛ]
      exact ⟨fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx, fun hv => ⟨v, hv, rfl⟩⟩
    have hΛ'' : ∀ v, v ∈ (C.M.X k).Λ ↔ v ∈ latG V (γ₁ * (γ * h)) := fun v => by
      have e : (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
          (((δ⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) = v := by
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
      have h0 := ((hS _).symm.trans (hΛ' (((δ⁻¹ : GL (Fin V.rank) D.host.E) :
        Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v))).trans (m1 _)
      rwa [e] at h0
    refine ⟨γ₁, hq, ⟨mul_mem hq hγ, ?_, ?_⟩, ?_⟩
    · rw [mul_assoc]
      ext v
      rw [SetLike.mem_coe, hΛ'']
      exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨x, hx, e⟩ => (show x = v from e) ▸ hx⟩
    · intro a ha
      obtain ⟨w, hw, hw'⟩ := hmk a ha
      have hta : C.F.t k a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) •
          (⊤ : Submodule (𝓞 D.host.E) (C.F.Di k).La) := by
        have h1 := Submodule.mem_map_of_mem (f := C.F.t k) ha
        rw [Submodule.map_smul''] at h1
        exact Submodule.smul_mono le_rfl le_top h1
      obtain ⟨b, hb⟩ := hcong _ hta
      rw [mul_assoc]
      refine ⟨(finHom V γ₁).1 *ᵥ w - finVec V (C.M.φ k b : Fin V.rank → D.host.E),
        sub_mem ((m2 w).1 hw) (markMove_finVec_mem V _ ((hΛ'' _).1 (C.M.φ k b).2)), ?_⟩
      have hw2 : finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) -
          (finHom V (γ * h)).1 *ᵥ (finVec V (C.ι a)) = (l.M : ℕ) • w := hw'
      have h3 := f1 (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E)
      rw [hb, markMove_finVec_add_nsmul] at h3
      show finVec V (C.M.φ k (C.F.t k a) : Fin V.rank → D.host.E) - _ = _
      rw [markMove_finHom_mul, nsmul_sub, ← markMove_mulVec_nsmul, ← hw2, Matrix.mulVec_sub, h3]
      abel
    · funext τ
      have a1 := ((GlobalTheory.Member.Arch.archM_spec D V C.θ hC.inf).1 τ.1).2.1 γ₁ (γ * h)
      have a2 := f2 τ.1 (C.θ τ.1) (hC.inf τ.1)
      show (archM V (C.θ τ.1) (γ₁ * γ * h) * C.x₀ τ.1 : Matrix _ _ ℂ) =
        (δ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ.1 * (archM V (C.θ τ.1) (γ * h) * C.x₀ τ.1)
      rw [mul_assoc γ₁, a1, a2, Matrix.mul_assoc]

end GlobalTheory.Member
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingRuleTranslateStableStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.markingRule_translate_stable : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k γ, C.Mark h k γ → (∀ γ₀ ∈ GQ V, C.Mark (γ₀ * h) k (γ * γ₀⁻¹)) ∧ (∀ u, FinCong V l.M u → C.Mark (h * u) k γ) ∧ (∀ u ∈ GinfC V, C.Mark (h * u) k γ) ∧ ∀ δ ∈ (C.M.X k).Γ, ∃ γ₁ ∈ GQ V, C.Mark h k (γ₁ * γ) ∧ C.fr (γ₁ * γ * h) k = lact δ (C.fr (γ * h) k) := by
  first | exact @GlobalTheory.Member.mark_move | exact GlobalTheory.Member.mark_move | (intros; apply GlobalTheory.Member.mark_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Exist

theorem exists_prime_mem_maximalIdeal_of_finite_residue (V : Type) [CommRing V] [IsLocalRing V]
    [Finite (IsLocalRing.ResidueField V)] : ∃ p : ℕ, p.Prime ∧ (p : V) ∈ IsLocalRing.maximalIdeal V := by
  obtain ⟨p, hp⟩ := CharP.exists (IsLocalRing.ResidueField V)
  refine ⟨p, CharP.char_is_prime (IsLocalRing.ResidueField V) p, ?_⟩
  rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem intFrExt_of_good : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c := by
  intro hP hN hB hT E _ _ _ H Dw l Xo c hpq hgood T io hfin x hx
  have : Finite (IsLocalRing.ResidueField T.V) := hfin
  obtain ⟨p, hp, hpm⟩ := exists_prime_mem_maximalIdeal_of_finite_residue T.V
  obtain ⟨O, _, β, Y, hPI, b, hb⟩ := GlobalTheory.T.exists_model_pushInvertible_over_completeDVR hP hN E H Dw l Xo c hpq T io p hp hpm (hgood p hp)
  have hIF := GlobalTheory.T.exists_integralFrames_model_invertible_pushforward hB hT E H Dw l Xo c
  let _ := io.toAlgebra
  obtain ⟨y₀, -, h0, -, -⟩ := gfp_frPt_gen (Xo := Xo) (c := c) (L := T.Fr) (L' := T.Fr) hT (fun _ => rfl) x hx
    (fun _ i j => if i = j then 1 else 0) (fun _ _ => if_pos rfl) (fun _ _ _ h => if_neg h.ne')
  obtain ⟨y, t, hbor⟩ := intFr_of_model hIF T io Y hPI b hb y₀
  refine ⟨T, RingHom.id _, 1, one_pos, fun z => by simp, hfin, y, ?_⟩
  have h1 : y.1.x = y₀.x := hbor.1
  have h2 : spMap (RingHom.id T.Fr) = 𝟙 _ := Spec.map_id _
  show y.1.x = _
  rw [h2, Category.id_comp, h1, h0]

end GlobalTheory.Exist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntFrExtOfGoodLevelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intFrExt_of_good_level : PartI → N1ab → Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → IntFrExt Xo c := by
  first | exact @GlobalTheory.Exist.intFrExt_of_good | exact GlobalTheory.Exist.intFrExt_of_good | (intros; apply GlobalTheory.Exist.intFrExt_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne
namespace GlobalTheory.MarkDet

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem prod_sub_prod {ι : Type} (M : ℕ) (s : Finset ι) (I : ι → FractionalIdeal (𝓞 E)⁰ E)
    (y z : ι → RA F E) (hy : ∀ i, y i ∈ hat1 F (I i : Set E)) (hz : ∀ i, z i ∈ hat1 F (I i : Set E)) :
    ∃ w ∈ hat1 F ((∏ i ∈ s, I i : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ i ∈ s, (y i + M • z i) - ∏ i ∈ s, y i = M • w := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, zero_mem _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨w, hw, e⟩ := ih
    have hp := prod_mem_adelicCompletionOfElementSet F s I y (fun i _ => hy i)
    have mul := (adelicCompletion_fractionalIdeal_properties F E).1 (I a) (∏ i ∈ s, I i)
    refine ⟨y a * w + z a * (∏ i ∈ s, y i + M • w), ?_, ?_⟩
    · rw [Finset.prod_insert ha]
      exact add_mem (mul _ (hy a) _ hw) (mul _ (hz a) _ (add_mem hp (nsmul_mem hw M)))
    · rw [Finset.prod_insert ha, Finset.prod_insert ha, sub_eq_iff_eq_add.1 e]
      simp only [nsmul_eq_mul]
      ring

theorem det_one_add_sub_one {n : ℕ} (M : ℕ) (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0)
    (K : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, K i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E), (1 + M • K).det - 1 = M • w := by
  have h1 : ∀ i j, (1 : Matrix (Fin n) (Fin n) (RA F E)) i j ∈
      hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_inv_cancel₀ (hc i), Algebra.TensorProduct.one_def]
      exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
    · rw [Matrix.one_apply_ne hij]
      exact zero_mem _
  have key : ∀ σ : Equiv.Perm (Fin n), ∃ w ∈ hat1 F ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E),
      ∏ j, (1 + M • K) (σ j) j - ∏ j, (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j = M • w := by
    intro σ
    have := prod_sub_prod F M Finset.univ (fun j => cI (σ j) * (cI j)⁻¹)
      (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j) (fun j => K (σ j) j)
      (fun j => h1 _ _) (fun j => h _ _)
    rw [Finset.prod_mul_distrib, Equiv.prod_comp σ cI, ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i)] at this
    exact this
  choose w hw e using key
  refine ⟨∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • w σ, sum_mem fun σ _ => ?_, ?_⟩
  · rw [Units.smul_def]
    exact zsmul_mem (hw σ) _
  · have d1 : (1 : RA F E) = (1 : Matrix (Fin n) (Fin n) (RA F E)).det := Matrix.det_one.symm
    rw [d1, Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [← smul_sub, e, Units.smul_def, Units.smul_def, smul_comm]

theorem det_sub_one_of_cong {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : ℕ) (hM : M ≠ 0)
    (G : Matrix (Fin n) (Fin n) (RA F E))
    (hg : ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ y ∈ hat F (L : Set (Fin n → E)), G *ᵥ z - z = M • y) :
    ∃ w ∈ hat1 F (Set.range (algebraMap (𝓞 E) E)), G.det - 1 = M • w := by
  have hone : ((1 : FractionalIdeal (𝓞 E)⁰ E) : Set E) = Set.range (algebraMap (𝓞 E) E) := by
    ext x
    exact FractionalIdeal.mem_one_iff _
  rw [← hone]
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w, P *ᵥ w ∈ hat F (L : Set (Fin n → E)) ↔ ∀ a, w a ∈ hat1 F (cI a : Set E) := by
    intro w; rw [hP]; exact key w
  have hMF : (M : F) ≠ 0 := Nat.cast_ne_zero.mpr hM
  obtain ⟨m, hm⟩ : ∃ m : RA F E, m * (M : RA F E) = 1 :=
    ⟨algebraMap F (RA F E) (M : F)⁻¹, by
      rw [← map_natCast (algebraMap F (RA F E)) M, ← map_mul, inv_mul_cancel₀ hMF, map_one]⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) (RA F E), N = m • (G - 1) := ⟨_, rfl⟩
  have hGN : G = 1 + M • N := by
    rw [hN, ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, mul_comm, hm, one_smul, add_sub_cancel]
  have hNz : ∀ z ∈ hat F (L : Set (Fin n → E)), N *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
    intro z hz
    obtain ⟨y, hy, ey⟩ := hg z hz
    rw [hN, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ey,
      ← Nat.cast_smul_eq_nsmul (RA F E), smul_smul, hm, one_smul]
    exact hy
  obtain ⟨k, hk0⟩ : ∃ k : Matrix (Fin n) (Fin n) (RA F E), k = Q * N * P := ⟨_, rfl⟩
  have hPk : P * k = N * P := by
    simp only [hk0, ← Matrix.mul_assoc, hPQ, Matrix.one_mul]
  have hkdet : (1 + M • k).det = G.det := by
    have h1 : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    have h2 : 1 + M • k = Q * G * P := by
      rw [hGN, hk0, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQP, Matrix.mul_smul, Matrix.smul_mul]
    rw [h2]
    simp only [Matrix.det_mul]
    linear_combination G.det * h1
  have hk : ∀ i j, k i j ∈ hat1 F ((cI i * (cI j)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
    intro i j
    refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
    have h1 : P *ᵥ (Pi.single j ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x)) ∈
        hat F (L : Set (Fin n → E)) := by
      rw [key']
      intro a
      by_cases ha : a = j
      · subst ha
        rw [Pi.single_eq_same]
        exact one_tmul_mem_adelicCompletionOfElementSet F hx
      · rw [Pi.single_eq_of_ne ha]
        exact zero_mem _
    have h2 := hNz _ h1
    rw [Matrix.mulVec_mulVec, ← hPk, ← Matrix.mulVec_mulVec, key'] at h2
    have h3 := h2 i
    rwa [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op] at h3
  rw [← hkdet]
  exact det_one_add_sub_one F M cI hc k hk

end General

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

theorem gLat_eq_of_finCong {D : D7} {V : HSp D} {N : ℕ} {u : GA D V} (hu : FinCong V N u) :
    gLat V u = latHat V := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact PrincLevel.finCong_map hu y hy
  · intro hz
    refine ⟨_, PrincLevel.finCong_map (PrincLevel.finCong_inv hu) z hz, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
      Matrix.one_mulVec]


end GlobalTheory.MarkDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoefChangeTypingsEquivOfValueWD
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.CoefChangeCompare

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing TensorProduct

section Algebra

variable {K K' : Type} [Field K] [Field K'] [CharZero K] [Algebra K K']

theorem exists_testRing_ext (p : TRing K) :
    ∃ (q : TRing K') (α : p.R →+* q.R), (∀ a, α (algebraMap K p.R a) = algebraMap K' q.R (algebraMap K K' a)) ∧
      (∀ (S : Type) [CommRing S] [Algebra K' S] (φ : p.R →+* S),
        (∀ a, φ (algebraMap K p.R a) = algebraMap K' S (algebraMap K K' a)) →
        ∃ β : q.R →ₐ[K'] S, ∀ v, β (α v) = φ v) ∧
      ∀ (m : ℕ) (b : Fin m → K') (v : Fin m → p.R), ∑ i, algebraMap K' q.R (b i) * α (v i) = 0 →
        ∀ lam : K' →ₗ[K] K, ∑ i, lam (b i) • v i = 0 := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K).2 p
  have hred' : IsReduced (K' ⊗[K] p.R) := GlobalTheory.ReducedAlg.isReduced_field_tensor _ _
  obtain ⟨q, ⟨e⟩⟩ := (GlobalTheory.reduced_finiteType_iff_testRing K').1 (K' ⊗[K] p.R) inferInstance hred'
  refine ⟨q, e.symm.toRingEquiv.toRingHom.comp (Algebra.TensorProduct.includeRight (R := K) (A := K') (B := p.R)).toRingHom,
    fun a => ?_, fun S _ _ φ hφ => ?_, fun m b v hv lam => ?_⟩
  · show e.symm (Algebra.TensorProduct.includeRight (algebraMap K p.R a)) = _
    rw [AlgHom.commutes, ← e.symm.commutes]
    rfl
  · letI : Algebra K S := ((algebraMap K' S).comp (algebraMap K K')).toAlgebra
    haveI : IsScalarTower K K' S := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let φ' : p.R →ₐ[K] S := { φ with commutes' := hφ }
    refine ⟨(Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)).comp e.toAlgHom,
      fun v => ?_⟩
    show Algebra.TensorProduct.lift (Algebra.ofId K' S) φ' (fun _ _ => Commute.all _ _)
      (e (e.symm ((1 : K') ⊗ₜ[K] v))) = _
    rw [e.apply_symm_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  · have h1 : ∑ i, b i ⊗ₜ[K] v i = (0 : K' ⊗[K] p.R) := by
      have h2 := congrArg e hv
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_zero, map_sum] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = e (algebraMap K' q.R (b i) * e.symm ((1 : K') ⊗ₜ[K] v i))
      rw [map_mul, e.commutes, e.apply_symm_apply, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp
    have h3 := congrArg (fun w => TensorProduct.lid K p.R (lam.rTensor p.R w)) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using h3

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c c' : Coeff l}

section First

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD

variable (c c') (hle : c.F ≤ c'.F)

abbrev inclF : c.F →+* c'.F := (IntermediateField.inclusion hle).toRingHom

def Compat (S : Type) [CommRing S] [Algebra c.F S] [Algebra c'.F S] : Prop :=
  ∀ a : c.F, algebraMap c'.F S (inclF c c' hle a) = algebraMap c.F S a

variable {c c'}

variable {r : ℕ}

end First

abbrev Natural (c : Coeff l) (f : Rul Xo c) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f

abbrev FromT {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y


variable (Xo c) in
abbrev ValueWD : Prop := EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)


variable (Xo c) in
abbrev HasBC : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z

theorem map_trans {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w :=
  frMap_trans (Xo := Xo) (c := c) _ _ _ φ ψ y z w h₁ h₂

theorem hasBC_of (hS : Out.SecBaseChangeSt) : HasBC Xo c :=
  GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c

theorem evR_spec {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : FromT y) :
    ∃ (p : TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : FrPt Xo c p.R), FrMap φ y₀ y ∧
      ∀ f : Rul Xo c, evR Xo c f y = φ (f p y₀) :=
  ⟨_, _, _, hy.choose_spec.choose_spec.choose_spec, fun f => by unfold evR evalAt; rw [dite_eq_left hy]⟩

theorem evR_not {S : Type} [CommRing S] [Algebra c.F S] {y : FrPt Xo c S} (hy : ¬ FromT y) (f : Rul Xo c) :
    evR Xo c f y = 0 := by
  unfold evR evalAt; rw [dite_eq_right hy]

theorem evR_test {f : Rul Xo c} (hf : Natural c f) (p : TRing c.F) (y : FrPt Xo c p.R) : evR Xo c f y = f p y := by
  obtain ⟨q, φ, y₀, h, e⟩ := evR_spec (y := y) ⟨p, AlgHom.id _ _, y, GlobalTheory.Frames.frMapUniq_refl y⟩
  rw [e, hf q p φ y₀ y h]

theorem evR_of_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S] [Algebra c.F S]
    {p : TRing c.F} {φ : p.R →ₐ[c.F] S} {y₀ : FrPt Xo c p.R} {y : FrPt Xo c S} (h : FrMap φ y₀ y) :
    evR Xo c f y = φ (f p y₀) := by
  obtain ⟨q, ψ, y₁, h₁, e⟩ := evR_spec (y := y) ⟨p, φ, y₀, h⟩
  rw [e]
  exact hWD f hf S q p ψ φ y₁ y₀ y h₁ h

theorem evR_map (hWD : ValueWD Xo c) {f : Rul Xo c} (hf : Natural c f) {S T : Type} [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T} {y : FrPt Xo c S} {z : FrPt Xo c T} (hy : FromT y)
    (h : FrMap φ y z) : evR Xo c f z = φ (evR Xo c f y) := by
  obtain ⟨p, ψ, y₀, h₀, e⟩ := evR_spec hy
  rw [e, evR_of_map hWD hf (map_trans ψ φ h₀ h)]
  rfl

theorem map_cancel (hBC : HasBC Xo c) {R S T : Type} [CommRing R] [Algebra c.F R] [CommRing S] [Algebra c.F S]
    [CommRing T] [Algebra c.F T] {α : R →ₐ[c.F] S} {β : S →ₐ[c.F] T} {φ : R →ₐ[c.F] T} (hc : β.comp α = φ)
    {y : FrPt Xo c R} {z : FrPt Xo c S} {w : FrPt Xo c T} (h₁ : FrMap α y z) (h₂ : FrMap φ y w) : FrMap β z w := by
  obtain ⟨w', hw'⟩ := hBC S T β z
  have h₃ : FrMap φ y w' := hc ▸ map_trans α β h₁ hw'
  rwa [(GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c R T φ y).1 w w' h₂ h₃]

theorem frBor_map {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] {φ : S →ₐ[c.F] T}
    {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (hb : FrBor t y y') (h : FrMap φ y z)
    (h' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, g1, g2, hg⟩ := (GlobalTheory.Frames.Model.frBor_iff t y y').1 hb
  refine (GlobalTheory.Frames.Model.frBor_iff _ z z').2 ⟨fun τ => (g τ).map φ, fun τ i => ?_, fun τ i j hij => ?_, ?_⟩
  · simp [g1]
  · simp [g2 τ i j hij]
  · exact (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg h).1 h'

variable (hle : c.F ≤ c'.F)

def resHom {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T) :
    Res hle S →ₐ[c.F] Res hle T :=
  { φ.toRingHom with commutes' := fun a => φ.commutes (incl hle a) }

theorem frMap_down {S T : Type} [CommRing S] [Algebra c'.F S] [CommRing T] [Algebra c'.F T] (φ : S →ₐ[c'.F] T)
    (y : FrPt Xo c' S) (z : FrPt Xo c' T) :
    FrMap (resHom hle φ) (ptDown hle y) (ptDown hle z) ↔ FrMap φ y z := Iff.rfl

theorem finite_incl : letI := (incl hle).toAlgebra; Module.Finite c.F c'.F := by
  letI := (incl hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  exact Module.Finite.of_restrictScalars_finite ℚ c.F c'.F

theorem exists_testRing_res (q : TRing c'.F) : ∃ p : TRing c.F, Nonempty (p.R ≃ₐ[c.F] Res hle q.R) := by
  obtain ⟨hft, hred⟩ := (GlobalTheory.reduced_finiteType_iff_testRing c'.F).2 q
  letI := (incl hle).toAlgebra
  haveI := finite_incl hle
  letI : Algebra c'.F (Res hle q.R) := inferInstanceAs (Algebra c'.F q.R)
  haveI : IsScalarTower c.F c'.F (Res hle q.R) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.FiniteType c'.F (Res hle q.R) := hft
  exact (GlobalTheory.reduced_finiteType_iff_testRing c.F).1 _ (Algebra.FiniteType.trans (S := c'.F) inferInstance this) hred

theorem fromT_down_test (hBC : HasBC Xo c) (q : TRing c'.F) (y : FrPt Xo c' q.R) : FromT (ptDown hle y) := by
  obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
  obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
  exact ⟨p, e, z, map_cancel hBC (by ext; simp) hz (GlobalTheory.Frames.frMapUniq_refl _)⟩

theorem fromT_down_iff (hBC : HasBC Xo c) {S : Type} [CommRing S] [Algebra c'.F S] (y : FrPt Xo c' S) :
    FromT (ptDown hle y) ↔ FromT y := by
  constructor
  · rintro ⟨p, φ, y₀, h⟩
    letI := (incl hle).toAlgebra
    obtain ⟨q, α, hα, hu, -⟩ := exists_testRing_ext (K' := c'.F) p
    obtain ⟨β, hβ⟩ := hu S φ.toRingHom φ.commutes
    let α' : p.R →ₐ[c.F] Res hle q.R := { α with commutes' := hα }
    obtain ⟨z, hz⟩ := hBC _ _ α' y₀
    exact ⟨q, β, ptUp hle z, map_cancel hBC (β := resHom hle β) (AlgHom.ext hβ) hz h⟩
  · rintro ⟨q, φ, y₀, h⟩
    obtain ⟨p, ψ, z, hz⟩ := fromT_down_test hle hBC q y₀
    exact ⟨p, _, z, map_trans ψ (resHom hle φ) hz h⟩

theorem evR_ruleUp (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {f : Rul Xo c} (hf : Natural c f) {S : Type} [CommRing S]
    [Algebra c'.F S] (y : FrPt Xo c' S) : evR Xo c' (ruleUp hle f) y = unRes (evR Xo c f (ptDown hle y)) := by
  by_cases hy : FromT y
  · obtain ⟨q, φ, y₀, h, e⟩ := evR_spec hy
    rw [e, evR_map hWD hf (fromT_down_test hle hBC q y₀) ((frMap_down hle φ y₀ y).2 h)]
    rfl
  · rw [evR_not hy, evR_not (fun h => hy ((fromT_down_iff hle hBC y).1 h)), map_zero]

theorem ruleUp_mem_sec (hWD : ValueWD Xo c) (hBC : HasBC Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : ruleUp hle f ∈ sec Xo c' a n := by
  refine ⟨fun p q φ y z h => ?_, fun q t y y' h => ?_⟩
  · exact evR_map hWD hf.1 (fromT_down_test hle hBC p y) ((frMap_down hle φ y z).2 h)
  · obtain ⟨p, ⟨e⟩⟩ := exists_testRing_res hle q
    obtain ⟨z, hz⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y)
    obtain ⟨z', hz'⟩ := hBC _ _ (e.symm : Res hle q.R →ₐ[c.F] p.R) (ptDown hle y')
    have he : (e : p.R →ₐ[c.F] Res hle q.R).comp (e.symm : Res hle q.R →ₐ[c.F] p.R) = AlgHom.id _ _ := by
      ext; simp
    have hb : FrBor (c := c) (S := Res hle q.R) t (ptDown hle y) (ptDown hle y') := h
    have hw := hf.2 p _ z z' (frBor_map hb hz hz')
    have e1 := evR_of_map hWD hf.1 (map_cancel hBC he hz (GlobalTheory.Frames.frMapUniq_refl _))
    have e2 := evR_of_map hWD hf.1 (map_cancel hBC he hz' (GlobalTheory.Frames.frMapUniq_refl _))
    have e3 : evR Xo c f (ptDown hle y') = wchar (S := Res hle q.R) (ex Dw a n) t * evR Xo c f (ptDown hle y) := by
      rw [e1, e2, hw, map_mul]
      congr 1
      unfold wchar
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_pow]
      exact congrArg (· ^ _) (e.apply_symm_apply _)
    exact e3

variable {r : ℕ}

end GlobalTheory.CoefChangeCompare
end
end
