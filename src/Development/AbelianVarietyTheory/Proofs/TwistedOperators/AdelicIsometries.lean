module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGLOfIsVecBasisAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCHyperbolicExtensionLatticeConjStable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalStabiliserScalesRestriction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsAdelicGlueVectorOfGlueBaseData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormSumWordCombinationCoefficientsLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitive
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.SelfDualGlue

variable {D : D7} {u : D.what₂.Word} {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V}

theorem vA_flat (x : X.V) (a : D.host.E) : vA Y (ι x + a • z) = mA Y X ι *ᵥ vA X x + inc D a • vA Y z := by
  rw [vA_add, vA_smul, mA_mulVec_vA]

theorem inc_hD_flat (h : IsLine Y X ι z u) (x x' : X.V) (a a' : D.host.E) :
    inc D (Y.hD (ι x + a • z) (ι x' + a' • z)) =
      hA X (vA X x) (vA X x') - inc D a * cjA D (inc D a') * inc D (Tu D u) := by
  rw [← hA_vA, vA_flat, vA_flat]
  exact hA_flat h _ _ _ _

theorem mem_glueLat_iff {L₀ : Lat X} {x₀ : X.V} (y : Y.V) : y ∈ glueLat Y X ι z u L₀ x₀ ↔
    ∃ x : X.V, Formalism.L2.Herm.crd X x ∈ L₀ ∧ ∃ a : 𝓞 D.host.E,
      y = ι (x + (a : D.host.E) • x₀) + ((a : D.host.E) * (Tu D u)⁻¹) • z := by
  rw [mem_glueLat]
  refine exists_congr fun x => and_congr_right fun _ => exists_congr fun a => ?_
  rw [map_add (f := _), map_smul, smul_add, smul_smul]
  constructor <;> rintro rfl <;> abel

theorem coords_of_mem (h : IsLine Y X ι z u) {L₀ : Lat X} {x₀ x : X.V} {a : D.host.E}
    (hm : ι x + a • z ∈ glueLat Y X ι z u L₀ x₀) :
    ∃ x₁ ∈ hat L₀, ∃ b ∈ OA D, vA X x = x₁ + b • vA X x₀ ∧ inc D a = b * inc D (Tu D u)⁻¹ := by
  have hv := vA_mem_hat Y hm
  rw [vA_flat, mem_hat_glueLat] at hv
  obtain ⟨x₁, hx₁, b, hb, e⟩ := hv
  obtain ⟨e1, e2⟩ := flat_inj h e
  exact ⟨x₁, hx₁, b, hb, e1, e2⟩

theorem mem_flatSp (x : X.V) (a : D.host.E) : ι x + a • z ∈ flatSp Y X ι z := Submodule.add_mem_sup (LinearMap.mem_range_self ι x)
    (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self z))


set_option maxHeartbeats 1600000 in
theorem isGlueVec_of_isSDIn : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  obtain ⟨-, -, hsd⟩ := hSD

  have key : ∀ (p : X.V) (α : D.host.E) (q : X.V) (β : D.host.E),
      ι p + α • z ∈ glueLat Y X ι z u L₀ x₀ → ι q + β • z ∈ glueLat Y X ι z u L₀ x₀ →
      hA X (vA X p) (vA X q) - inc D α * cjA D (inc D β) * inc D (Tu D u) ∈ OA D := by
    intro p α q β hp hq
    rw [← inc_hD_flat h, inc_mem_iff]
    exact (hsd _ (mem_flatSp (ι := ι) (z := z) q β)).1 hq _ hp

  have hX : ∀ p : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → ι p + (0 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    intro p hp
    rw [mem_glueLat_iff]
    exact ⟨p, hp, 0, by simp⟩
  have hg : ι x₀ + (Tu D u)⁻¹ • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [mem_glueLat_iff]
    exact ⟨0, by simp, 1, by simp⟩
  have hv : ∀ y : Fin X.rank → D.host.E,
      (fun i => inc D (y i)) = vA X ((Formalism.L2.Herm.crd X).symm y) := by
    intro y
    funext i
    simp [vA]
  have hrat : ∀ p q : X.V, Formalism.L2.Herm.crd X p ∈ L₀ → Formalism.L2.Herm.crd X q ∈ L₀ →
      hA X (vA X p) (vA X q) ∈ OA D := by
    intro p q hp hq
    simpa using key p 0 q 0 (hX p hp) (hX q hq)

  have hright : ∀ f, (∀ y ∈ L₀, hA X f (fun i => inc D (y i)) ∈ OA D) →
      ∀ y ∈ hat L₀, hA X f y ∈ OA D := by
    intro f hf y hy
    refine hat_induction (p := fun y => hA X f y ∈ OA D) hf ?_ ?_ ?_ hy
    · show hA X f 0 ∈ OA D
      rw [hA_zero_right]
      exact zero_mem _
    · intro a b ha hb
      show hA X f (a + b) ∈ OA D
      rw [hA_add_right]
      exact add_mem ha hb
    · intro a ha b hb
      show hA X f (a • b) ∈ OA D
      rw [hA_smul_right]
      exact mul_mem (cjA_mem ha) hb
  have hint : ∀ x ∈ hat L₀, ∀ y ∈ hat L₀, hA X x y ∈ OA D := by
    intro x hx
    refine hright x fun y hy => hA_mem_of_forall (fun x' hx' => ?_) x hx
    rw [hv x', hv y]
    exact hrat _ _ (by simpa using hx') (by simpa using hy)

  have hz : ι 0 + (1 : D.host.E) • z ∈ glueLat Y X ι z u L₀ x₀ := by
    rw [map_zero, zero_add]
    exact (hP 1).2 (one_mem _)
  obtain ⟨x₁, hx₁, b, -, e1, e2⟩ := coords_of_mem h hz
  have hb : b = inc D (Tu D u) := by
    rw [map_one] at e2
    calc b = b * (inc D (Tu D u)⁻¹ * inc D (Tu D u)) := by rw [inc_inv_mul, mul_one]
      _ = inc D (Tu D u) := by rw [← mul_assoc, ← e2, one_mul]
  have h0 : vA X (0 : X.V) = 0 := by simpa using vA_add X (0 : X.V) 0
  refine ⟨?_, hint, ?_, ?_, ?_⟩
  · rw [h0] at e1
    rw [← hb, eq_sub_of_add_eq' e1.symm]
    exact sub_mem_hat zero_mem_hat hx₁
  · refine hright (vA X x₀) fun y hy => ?_
    rw [hv y]
    simpa using key x₀ (Tu D u)⁻¹ _ 0 hg (hX _ (by simpa using hy))
  · have := key x₀ (Tu D u)⁻¹ x₀ (Tu D u)⁻¹ hg hg
    rwa [cjA_inc_inv, mul_assoc, inc_inv_mul, mul_one] at this
  ·

    intro y hy
    obtain ⟨y₀, hy₀⟩ := exists_sub_inc_mem_hat hlat.span_eq_top y
    obtain ⟨q, rfl⟩ := (Formalism.L2.Herm.crd X).surjective y₀
    change y - vA X q ∈ hat L₀ at hy₀
    have hq : ι q + X.hD q x₀ • z ∈ glueLat Y X ι z u L₀ x₀ := by
      refine (hsd _ (mem_flatSp (ι := ι) (z := z) q (X.hD q x₀))).2 fun v hv' => ?_
      obtain ⟨p, hp, a, rfl⟩ := (mem_glueLat_iff v).1 hv'
      have hp' : vA X p ∈ hat L₀ := inc_mem_hat hp
      have h1 : hA X (vA X p) (vA X q) ∈ OA D := by
        rw [show vA X q = y - (y - vA X q) from (sub_sub_cancel y (vA X q)).symm, hA_sub_right]
        exact sub_mem (hy _ hp') (hint _ hp' _ hy₀)
      rw [← inc_mem_iff, inc_hD_flat h, ← hA_vA X q x₀, cjA_hA, vA_add, vA_smul, hA_add_left,
        hA_smul_left, map_mul (inc D)]
      convert h1 using 1
      linear_combination (-(inc D (a : D.host.E) * hA X (vA X x₀) (vA X q))) * inc_inv_mul u
    obtain ⟨x₂, hx₂, c, hc, e3, -⟩ := coords_of_mem h hq
    refine ⟨c, hc, ?_⟩
    have e4 : y - c • vA X x₀ = (y - vA X q) + x₂ := by
      rw [e3]
      abel
    rw [e4]
    exact add_mem_hat hy₀ hx₂

end GlobalTheory.AdIsom.SelfDualGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAdelicGlueVectorOfSelfDualPrimitiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V), IsLine Y X ι z u → ∀ (L₀ : Lat X) (x₀ : X.V), Submodule.IsFullLattice D.host.E L₀ → IsSDIn Y (flatSp Y X ι z) (glueLat Y X ι z u L₀ x₀) → IsPrim Y z (glueLat Y X ι z u L₀ x₀) → IsGlueVec X u L₀ (vA X x₀) := by
  intro D u Y X ι z h L₀ x₀ hlat hSD hP
  letI := hlat
  exact GlobalTheory.AdIsom.SelfDualGlue.isGlueVec_of_isSDIn D u Y X ι z h L₀ x₀
    (by first | exact hlat | infer_instance) hSD hP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVector
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVector
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdIsom.GlueBase

open GlobalTheory.IdemSupport (cP)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem split_prime {e a t t' : A} (ht : t' * t = 1) {y f : M} (hy : e • y = y) :
    y = e • (y - a • f) + (a * (e * t')) • (t • f) := by
  have key : a * (e * t') * t = e * a := by linear_combination (a * e) * ht
  rw [smul_sub, hy, smul_smul, smul_smul, key, sub_add_cancel]

theorem mem_of_mul_sub (S : Subring A) {b h t : A} (hb : b ∈ S) (h1 : b * h ∈ S) (h2 : h - t ∈ S) : b * t ∈ S := by
  have hd := S.sub_mem h1 (S.mul_mem hb h2)
  rwa [mul_sub, sub_sub_cancel] at hd

theorem mem_of_sub (S : Subring A) {a b : A} (ha : a ∈ S) (h : a - b ∈ S) : b ∈ S := by
  have hd := S.sub_mem ha h
  rwa [sub_sub_cancel] at hd

theorem idem_smul_smul {e : A} (he : e * e = e) (x : M) : e • e • x = e • x := by
  rw [smul_smul, he]

end Alg

variable {D : D7}

theorem inc_inv_mul (u : D.what₂.Word) : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (Tu_ne_zero u), map_one]

theorem cjA_inc_inv (u : D.what₂.Word) : cjA D (inc D (Tu D u)⁻¹) = inc D (Tu D u)⁻¹ := by
  rw [cjA_inc]
  congr 1
  simp [Tu, star_inv₀]

theorem hA_idem {X : HSp D} {e : EAf D} {y : Fin X.rank → EAf D} (hy : cjA D e • y = y) (x : Fin X.rank → EAf D) :
    hA X x y = hA X (e • x) y := by
  conv_lhs => rw [← hy]
  rw [hA_smul_right, hA_smul_left, cjA_cjA]

theorem isBasePair_of_isGlueVec (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E) (hπ : IsPi u π) (X : HSp D) (L₀ : Lat X)
    (f : Fin X.rank → EAf D) (hL : Submodule.IsFullLattice D.host.E L₀) (hf : IsGlueVec X u L₀ f) :
    IsBasePair X u π L₀ fun w => idem w • f := by
  have ht : inc D (Tu D u)⁻¹ * inc D (Tu D u) = 1 := inc_inv_mul u
  have := hL
  unfold IsBasePair
  refine ⟨by infer_instance, fun w e he hT y => ?_, fun w e he hπw => ?_⟩
  ·
    obtain rfl := eq_idem he
    have hinv : idem w * inc D (Tu D u)⁻¹ ∈ OA D := (idem_mul_inv_mem_iff u w).2 hT
    simp only [InCmp]
    constructor
    · rintro ⟨hy, hey⟩
      exact ⟨(mem_hat_dualL_iff hL y).2 fun x hx => hf.int x hx y hy, hey⟩
    · rintro ⟨hy, hey⟩
      obtain ⟨a, ha, hya⟩ := hf.dual y ((mem_hat_dualL_iff hL y).1 hy)
      refine ⟨?_, hey⟩
      rw [split_prime (a := a) (f := f) ht hey]
      exact add_mem_hat (smul_mem_hat (idem_mem w) hya) (smul_mem_hat ((OA D).mul_mem ha hinv) hf.mul_mem)
  ·
    obtain rfl := eq_idem he
    have hTw : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ w.asIdeal := by
      rw [← pi_mul_cO hπ]
      exact w.asIdeal.mul_mem_right _ hπw
    have hnot : idem w * inc D (Tu D u)⁻¹ ∉ OA D := fun h => (idem_mul_inv_mem_iff u w).1 h hTw
    have hff : hA X f f - inc D (Tu D u)⁻¹ ∈ OA D := hf.norm
    refine ⟨idem_smul_smul (idem_mul_self w) f, ?_, ?_, ?_⟩
    · show inc D (Tu D u) • (idem w • f) ∈ hat L₀
      rw [smul_smul, mul_comm, ← smul_smul]
      exact smul_mem_hat (idem_mem w) hf.mul_mem
    ·
      intro hmem
      apply hnot
      refine mem_of_mul_sub (OA D) (idem_mem w) ?_ hff
      rw [← hA_smul_left, ← cjA_hA]
      exact cjA_mem (hf.pair _ hmem)
    · intro y
      simp only [InCmp]
      constructor
      · rintro ⟨hy, hey⟩
        refine ⟨hey, fun x hx => hf.int x hx.1 y hy, ?_⟩
        rw [hA_smul_left]
        exact (OA D).mul_mem (idem_mem w) (hf.pair y hy)
      · rintro ⟨hey, hx, hfy⟩
        have hdual : ∀ x ∈ hat L₀, hA X x y ∈ OA D := by
          intro x hx'
          rw [hA_idem hey]
          exact hx _ ⟨smul_mem_hat (idem_mem w) hx', idem_smul_smul (idem_mul_self w) x⟩
        obtain ⟨a, ha, hya⟩ := hf.dual y hdual
        refine ⟨?_, hey⟩
        have h1 : cjA D a * idem w * hA X f f ∈ OA D := by
          have hp : hA X (idem w • f) (a • f) ∈ OA D := by
            refine mem_of_sub (OA D) hfy ?_
            rw [← hA_sub_right, hA_smul_left]
            exact (OA D).mul_mem (idem_mem w) (hf.pair _ hya)
          rwa [hA_smul_left, hA_smul_right, ← mul_assoc, mul_comm (idem w)] at hp
        have h2 : cjA D a * idem w * inc D (Tu D u)⁻¹ ∈ OA D :=
          mem_of_mul_sub (OA D) ((OA D).mul_mem (cjA_mem ha) (idem_mem w)) h1 hff
        have h3 : a * (cjA D (idem w) * inc D (Tu D u)⁻¹) ∈ OA D := by
          have hc := cjA_mem h2
          rwa [map_mul, map_mul, cjA_cjA, cjA_inc_inv, mul_assoc] at hc
        rw [split_prime (a := a) (f := f) ht hey]
        exact add_mem_hat (smul_mem_hat (cjA_mem (idem_mem w)) hya) (smul_mem_hat h3 hf.mul_mem)

end GlobalTheory.AdIsom.GlueBase
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsGlueBaseDataOfIsAdelicGlueVectorStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector : ∀ (D : D7) (u : D.what₂.Word) (π : 𝓞 D.host.E), IsPi u π → ∀ (X : HSp D) (L₀ : Lat X) (f : Fin X.rank → EAf D), Submodule.IsFullLattice D.host.E L₀ → IsGlueVec X u L₀ f → IsBasePair X u π L₀ fun w => idem w • f := by
  first | exact @GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | exact GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec | (intros; apply GlobalTheory.AdIsom.GlueBase.isBasePair_of_isGlueVec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizer
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom

namespace GlobalTheory.TransportUnique

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {A : Type} [CommRing A]

theorem exists_inv {m n : ℕ} {x : Matrix (Fin m) (Fin n) A}
    (h : Function.Bijective (x.mulVec : (Fin n → A) → (Fin m → A))) :
    ∃ y : Matrix (Fin n) (Fin m) A, y * x = 1 ∧ x * y = 1 := by
  let e : (Fin n → A) ≃ₗ[A] (Fin m → A) := LinearEquiv.ofBijective (Matrix.toLin' x) h
  have hx : x = LinearMap.toMatrix' e.toLinearMap := (LinearMap.toMatrix'_toLin' x).symm
  refine ⟨LinearMap.toMatrix' e.symm.toLinearMap, ?_, ?_⟩
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp
  · rw [hx, ← LinearMap.toMatrix'_comp]
    simp

theorem hform_mulVec (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ (Formalism.UG.cT σ k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform σ J a b = (σ ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : σ ∘ (k *ᵥ a) = (σ ∘ a) ᵥ* Formalism.UG.cT σ k := by
    funext i
    rw [Formalism.UG.cT, vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]

theorem unitary_iff (σ : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT σ k * J * k = J ↔ ∀ a b, Formalism.UG.hform σ J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform σ J a b := by
  refine ⟨fun h a b => by rw [hform_mulVec, h], fun h => ?_⟩
  ext i j
  have := h (Pi.single i 1) (Pi.single j 1)
  rw [hform_mulVec] at this
  simpa [Formalism.UG.hform, Pi.single_apply, apply_ite σ] using this

theorem smul_eq_of_fix {m n : ℕ} {e : A} (β : GL (Fin m) A) {B : Matrix (Fin m) (Fin n) A}
    {k : Matrix (Fin m) (Fin m) A} (h : ∀ j, ∃ c, e • (β.val *ᵥ Pi.single j 1) = B *ᵥ c) (hk : k * B = B) :
    e • k = e • (1 : Matrix (Fin m) (Fin m) A) := by
  have h1 : k * (e • β.val) = e • β.val := by
    ext i j
    obtain ⟨c, hc⟩ := h j
    have : k *ᵥ (e • (β.val *ᵥ Pi.single j 1)) = e • (β.val *ᵥ Pi.single j 1) := by
      rw [hc, mulVec_mulVec, hk]
    have := congrFun this i
    simpa [Matrix.mul_apply, mulVec, dotProduct, Pi.single_apply] using this
  have h2 := congrArg (· * (β⁻¹).val) h1
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using h2

theorem fix_of_smul_eq {m n : ℕ} {e : A} {B : Matrix (Fin m) (Fin n) A} {k : Matrix (Fin m) (Fin m) A}
    (h : e • k = e • (1 : Matrix (Fin m) (Fin m) A)) (hB : e • B = B) : k * B = B := by
  rw [← hB, Matrix.mul_smul, ← Matrix.smul_mul, h, Matrix.smul_mul, Matrix.one_mul]

theorem conj_smul_eq (σ : A →+* A) (hσ : ∀ a, σ (σ a) = a) {n : ℕ} {J k : Matrix (Fin n) (Fin n) A} (hJ : IsUnit J)
    (hk : Formalism.UG.cT σ k * J * k = J) {e : A} (he : e • k = e • (1 : Matrix (Fin n) (Fin n) A)) :
    σ e • k = σ e • (1 : Matrix (Fin n) (Fin n) A) := by
  have h1 : (e • Formalism.UG.cT σ k) * J = (e • (1 : Matrix (Fin n) (Fin n) A)) * J := by
    calc (e • Formalism.UG.cT σ k) * J = Formalism.UG.cT σ k * J * (e • (1 : Matrix (Fin n) (Fin n) A)) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
      _ = _ := by rw [← he, Matrix.mul_smul, hk, he, Matrix.smul_mul, Matrix.one_mul]
  have h2 := hJ.mul_right_cancel h1
  ext i j
  have := congrArg σ (congrFun (congrFun h2 j) i)
  simpa [Formalism.UG.cT, hσ, Matrix.one_apply, apply_ite σ, eq_comm] using this

theorem bc_eq_one_iff {B : Type} [CommRing B] (φ : A →+* B) {n : ℕ} (k : GL (Fin n) A) :
    Formalism.UG.bc φ k = 1 ↔ ∀ i j, φ (k.val i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := by
  rw [Units.ext_iff, ← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero]
  simp [Formalism.UG.bc, Matrix.one_apply, apply_ite φ]

end Gen

variable {D : D7}

theorem idem_smul_iff (w : Pl D.host.E) {n : ℕ} (k l : Matrix (Fin n) (Fin n) (EAf D)) :
    idem w • k = idem w • l ↔ ∀ i j, GlobalTheory.StdFrames.cpt w (k i j - l i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [RingHom.map_sub, sub_eq_zero, ← idem_mul_eq_iff]
  rfl

theorem bc_prV_eq_one_iff (w : Pl D.host.E) {n : ℕ} (k : GL (Fin n) (EAf D)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) (w.under (𝓞 D.host.F))) k = 1 ↔
      idem w • k.val = idem w • (1 : Matrix (Fin n) (Fin n) (EAf D)) ∧
      idem (GlobalTheory.IdemSupport.cP w) • k.val = idem (GlobalTheory.IdemSupport.cP w) • (1 : Matrix (Fin n) (Fin n) (EAf D)) := by
  rw [idem_smul_iff, idem_smul_iff]
  refine (bc_eq_one_iff _ k).trans ?_
  have h := fun z => GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (GlobalTheory.StdFrames.toAd_spec D) (w.under (𝓞 D.host.F)) z
  constructor
  · intro H
    exact ⟨fun i j => (h _).1 (H i j) w rfl, fun i j => (h _).1 (H i j) _ (GlobalTheory.IdemSupport.under_cP w)⟩
  · rintro ⟨H1, H2⟩ i j
    refine (h _).2 fun P hP => ?_
    rcases GlobalTheory.IdemSupport.eq_or_eq_cP hP with rfl | rfl
    · exact H1 i j
    · exact H2 i j

theorem mem_level_iff (W : HSp D) (L : Lat W) (k : GL (Fin W.rank) (EAf D)) :
    k ∈ Formalism.UG.levelAfL D.sp.cm.sig W.gram L ↔
      Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) ∧
        ∀ a, a ∈ hat L ↔ k.val *ᵥ a ∈ hat L := Iff.rfl

theorem col_mem_gen {A : Type} [CommRing A] (S : Subring A) {n : ℕ} (β : GL (Fin n) A) (j i : Fin n) :
    ((β⁻¹).val *ᵥ (β.val *ᵥ Pi.single j 1)) i ∈ S := by
  rw [mulVec_mulVec, Units.inv_mul, one_mulVec, Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem idem_smul_eq_of_fix {W : HSp D} {L : Lat W} (hL : Submodule.IsFullLattice D.host.E L) {w : Pl D.host.E} {n : ℕ}
    {B : Matrix (Fin W.rank) (Fin n) (EAf D)} (hB : IsBasisAt W w L B) {k : Matrix (Fin W.rank) (Fin W.rank) (EAf D)}
    (h1 : HMul.hMul k B = B) : idem w • k = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  obtain ⟨-, e, he, -, hc⟩ := hB
  obtain rfl := eq_idem he
  obtain ⟨β, rfl⟩ := GlobalTheory.AdIsom.exists_eq_lat (D := D) (Λ := L) hL
  refine smul_eq_of_fix β (fun j => ?_) h1
  have h := (mem_hat_lat β _).2 (col_mem_gen (OA D) β j)
  obtain ⟨c, hc'⟩ := (hc _).1 ⟨smul_mem_hat (idem_mem w) h, by rw [smul_smul, idem_mul_self]⟩
  exact ⟨_, hc'⟩

theorem transport_unique : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S _ n be be' hL hbe x hx x'
  obtain ⟨⟨hb, hf⟩, hl, hs⟩ := hx
  constructor
  · rintro ⟨⟨hb', hf'⟩, hl', hs'⟩
    obtain ⟨y, y1, y2⟩ := exists_inv hb
    obtain ⟨y', y1', y2'⟩ := exists_inv hb'
    let k : GL (Fin W.rank) (EAf D) := ⟨HMul.hMul y x', HMul.hMul y' x,
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x', y2', Matrix.one_mul, y1],
      by rw [Matrix.mul_assoc, ← Matrix.mul_assoc x, y2, Matrix.one_mul, y1']⟩
    have hk : HMul.hMul x k.val = x' := by
      change HMul.hMul x (HMul.hMul y x') = x'
      rw [← Matrix.mul_assoc, y2, Matrix.one_mul]
    have hkv : ∀ a, x *ᵥ (k.val *ᵥ a) = x' *ᵥ a := fun a => by rw [mulVec_mulVec, hk]
    have hU : Formalism.UG.cT (cjA D) k.val * W.gram.map (inc D) * k.val = W.gram.map (inc D) :=
      (unitary_iff _ _ _).2 fun a b => by
        rw [← hA_eq, ← hA_eq, ← hf, hkv, hkv, hf']
    refine ⟨k, ⟨(mem_level_iff W L k).2 ⟨hU, fun a => ?_⟩, fun w hw => ?_⟩, hk.symm⟩
    · rw [hl (k.val *ᵥ a), hkv, hl']
    · have h1 : HMul.hMul k.val (be w) = be w := by
        change HMul.hMul (HMul.hMul y x') (be w) = be w
        rw [Matrix.mul_assoc, hs' w hw, ← hs w hw, ← Matrix.mul_assoc, y1, Matrix.one_mul]
      have h2 : idem w • k.val = idem w • (1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) :=
        idem_smul_eq_of_fix hL (hbe w hw) h1
      refine (bc_prV_eq_one_iff w k).2 ⟨h2, ?_⟩
      rw [← cjA_idem]
      exact conj_smul_eq (cjA D) cjA_cjA (GlobalTheory.StdFrames.isUnit_gram W) hU h2
  · rintro ⟨k, ⟨hk, hk1⟩, rfl⟩
    obtain ⟨hU, hst⟩ := (mem_level_iff W L k).1 hk
    refine ⟨⟨?_, fun a b => ?_⟩, fun a => ?_, fun w hw => ?_⟩
    · have : (HMul.hMul x k.val : Matrix (Fin Y.rank) (Fin W.rank) (EAf D)).mulVec = x.mulVec ∘ k.val.mulVec := funext fun a => (mulVec_mulVec _ _ _).symm
      rw [this]
      refine hb.comp (Function.bijective_iff_has_inverse.2 ⟨(k⁻¹).val.mulVec, fun a => ?_, fun a => ?_⟩)
      · rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      · rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
    · rw [← mulVec_mulVec, ← mulVec_mulVec, hf, hA_eq, hA_eq]
      exact (unitary_iff _ _ _).1 hU b a
    · rw [← mulVec_mulVec, ← hl, ← hst]
    · obtain ⟨-, e, he, hB, -⟩ := hbe w hw
      obtain rfl := eq_idem he
      have h2 := ((bc_prV_eq_one_iff w k).1 (hk1 w hw)).1
      have h3 : HMul.hMul k.val (be w) = be w := fix_of_smul_eq h2 hB
      rw [Matrix.mul_assoc, h3, hs w hw]

end GlobalTheory.TransportUnique

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicIsometryTransportUniqueModStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer : ∀ (D : D7) (W Y : HSp D) (L : Lat W) (Λ : Lat Y) (S : Finset (Pl D.host.E)), IsSplitSet S → ∀ (n : ℕ) (be : Pl D.host.E → Matrix (Fin W.rank) (Fin n) (EAf D)) (be' : Pl D.host.E → Matrix (Fin Y.rank) (Fin n) (EAf D)), Submodule.IsFullLattice D.host.E L → (∀ w ∈ S, IsBasisAt W w L (be w)) → ∀ x, IsTransport W Y L Λ S be be' x → ∀ x', IsTransport W Y L Λ S be be' x' ↔ ∃ k, InStabAway W L S k ∧ x' = HMul.hMul x (k.1 : Matrix (Fin W.rank) (Fin W.rank) (EAf D)) := by
  intro D W Y L Λ S hS n be be' hL hbe x hx x'
  first
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL hbe x hx x'
  | exact GlobalTheory.TransportUnique.transport_unique D W Y L Λ S hS n be be' hL.toIsLattice hbe x hx x' 
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdeal
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  intro D
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hs : ∀ x : D.host.E, star x = ReciprocityTheory.ChartRestriction.G.FD.cc x := fun _ => rfl
  have hcc : ∀ a : D.host.E, ReciprocityTheory.ChartRestriction.G.FD.cc a = D.host.conj a := fun a => bridge_star_holds D.R D.host a
  have key : ∀ nn : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E, nn ≠ 0 → GlobalTheory.conjFrac nn = nn →
      GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) nn := fun nn h0 h =>
    ⟨h0, fun x => by rw [hs, ← GlobalTheory.mem_conjFrac, h]⟩
  have hb : D.host.AAbar = GlobalTheory.conjFrac D.host.AA := by
    ext a
    rw [GlobalTheory.mem_conjFrac, hcc]
    exact ⟨Formalism.L2.Pj.conj_mem_AA D, fun ha => by
      simpa only [Formalism.L2.Pj.conj_conj] using Formalism.L2.Pj.conj_mem_AAbar D ha⟩
  have hA : D.host.AA ≠ 0 := Formalism.L2.Pj.AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D
  have hg : (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  refine ⟨key _ (inv_ne_zero GlobalTheory.coe_different_ne_zero) ?_, key _ ?_ ?_⟩
  · rw [GlobalTheory.conjFrac_inv]
    exact congrArg _ GlobalTheory.conjFrac_different
  · rw [hb]
    exact mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hg) hA) (GlobalTheory.conjFrac_ne_zero hA)
  · have hc : ReciprocityTheory.ChartRestriction.G.FD.cc (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ =
        (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ := by
      rw [hcc, map_inv₀, map_natCast]
    rw [hb, map_mul, map_mul, GlobalTheory.conjFrac_spanSingleton, GlobalTheory.conjFrac_conjFrac, hc, mul_right_comm]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjStableInverseDifferentAndNormIdealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) ((D.host.ddE : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E))⁻¹ ∧ GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable (D := D) (FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))⁻¹ * D.host.AA * D.host.AAbar) := by
  first | exact @GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | exact GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal | (intros; apply GlobalTheory.Twist.isCStable_inv_different_and_norm_ideal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProof
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProof
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

theorem star_eq_conj (D : D7) (x : D.host.E) : star x = D.host.conj x := by
  have := D.host.der.cm
  obtain ⟨ψ⟩ := (inferInstance : Nonempty (D.host.E →+* ℂ))
  have hc : ∀ y, ψ (D.host.conj y) = starRingEnd ℂ (ψ y) :=
    (D.host.der.conj_iff ψ D.host.conj).2 (MulEquiv.apply_symm_apply _ _)
  apply ψ.injective
  rw [hc]
  exact NumberField.IsCMField.complexEmbedding_complexConj _ ψ x

theorem hT_zero_symm {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E) {x y : S.V}
    (h : S.hT x y = 0) : S.hT y x = 0 := by
  rw [← S.herm.eq x y, h, map_zero]

theorem isDec_smul (D : D7) (t : D.host.E) :
    IsDec (D.sp.Y 0) (D.sp.X 0) (D.sp.iXY 0) (fun _ : Fin 1 => t • D.sp.zm)
      (-(t * star t * ((D.mem D.u₀).A.T : D.host.E))) D.sp.hypE D.sp.hypF := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hsym : ∀ a b : (D.sp.Y 0).V, (D.sp.Y 0).hT a b = 0 → (D.sp.Y 0).hT b a = 0 :=
    fun a b h => hT_zero_symm (D.sp.Y 0) h
  refine
    { isom := D.sp.iXY_isom 0 hm
      a_le := le_rfl
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := ?_
      ff := ?_
      ef := ?_
      hyp_X := ?_
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [D.sp.Y_rank 0 (Nat.zero_le _), D.sp.X_rank 0 (Nat.zero_le _)]
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rankY, Formalism.BasicNotions.Ranks.N, Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
    omega
  · intro i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, map_smul, D.sp.zm_norm, starRingEnd_apply, smul_eq_mul,
      D.sp_T]
    ring
  · intro i x
    simp only [HSpace.hD, LinearMap.map_smulₛₗ₂, hsym _ _ (D.sp.zm_orth x), smul_zero]
  · intro i j
    exact D.sp.hyp_ee j i
  · intro i j
    exact D.sp.hyp_ff j i
  · intro i j
    simp only [HSpace.hD]
    rw [← (D.sp.Y 0).herm.eq (D.sp.hypE i) (D.sp.hypF j), D.sp.hyp_ef]
    split_ifs <;> simp
  · intro i x
    exact ⟨hsym _ _ (D.sp.hyp_orthX i x).1, hsym _ _ (D.sp.hyp_orthX i x).2⟩
  · intro i j
    simp only [HSpace.hD, map_smul, hsym _ _ (D.sp.hyp_orthz i).1, hsym _ _ (D.sp.hyp_orthz i).2, smul_zero,
      and_self]

theorem recordDec (D : D7) : RecordDecSt D := by
  refine ⟨fun u => ?_, ?_⟩
  · have hc0 := D.cOf_ne u
    have hc1 : D.host.conj (D.cOf u) ≠ 0 := (map_ne_zero _).2 hc0
    have h := isDec_smul D (D.cOf u)⁻¹
    have hs : -((D.cOf u)⁻¹ * star (D.cOf u)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -Tu D u := by
      rw [star_inv₀, star_eq_conj, ← D.cOf_eq u]
      field_simp
    rw [hs] at h
    exact h
  · obtain ⟨π, -, hπ, -⟩ := D.T_norm D.u₀
    have hT : ((D.mem D.u₀).A.T : D.host.E) ≠ 0 := by
      rw [← D.sp_T]
      exact_mod_cast D.sp.T_prime.ne_zero
    have hπ0 : (π : D.host.E) ≠ 0 := by
      rintro h0
      rw [h0, zero_mul] at hπ
      exact hT hπ.symm
    have hπ1 : D.host.conj (π : D.host.E) ≠ 0 := (map_ne_zero _).2 hπ0
    refine ⟨(π : D.host.E)⁻¹ • D.sp.zm, ?_⟩
    have h := isDec_smul D (π : D.host.E)⁻¹
    have hs : -((π : D.host.E)⁻¹ * star (π : D.host.E)⁻¹ * ((D.mem D.u₀).A.T : D.host.E)) = -1 := by
      rw [star_inv₀, star_eq_conj, ← hπ]
      field_simp
    rw [hs] at h
    exact h

end GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProofStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  first | exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | exact GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | (intros; apply GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometry
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometry
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.StdIsom
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents

variable {D : D7}

def sumMap (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) →ₗ[D.host.E] Y.V :=
  ι.coprod ((Fintype.linearCombination D.host.E z).coprod
    ((Fintype.linearCombination D.host.E e).coprod (Fintype.linearCombination D.host.E f)))

theorem sumMap_apply (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) {a ρ : ℕ} (z : Fin a → Y.V) (e f : Fin ρ → Y.V)
    (p : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    sumMap Y X ι z e f p = ι p.1 + (∑ i, p.2.1 i • z i + (∑ i, p.2.2.1 i • e i + ∑ i, p.2.2.2 i • f i)) := by
  simp [sumMap, Fintype.linearCombination_apply]

theorem hT_swap (Y : HSp D) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

theorem form_sumMap {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f)
    (p q : X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) :
    Y.hT (sumMap Y X ι z e f p) (sumMap Y X ι z e f q) =
      X.hT p.1 q.1 + (∑ i, star (p.2.1 i) * q.2.1 i * c +
        (∑ i, star (p.2.2.1 i) * q.2.2.2 i + ∑ i, star (p.2.2.2 i) * q.2.2.1 i)) := by
  have hsub : Subsingleton (Fin a) := by
    have := h.a_le
    exact ⟨fun i j => Fin.ext (by omega)⟩
  have zz : ∀ i j, Y.hT (z i) (z j) = if i = j then c else 0 := fun i j => by
    obtain rfl := Subsingleton.elim i j
    rw [if_pos rfl]; exact h.z_norm i
  have zx : ∀ i x, Y.hT (z i) (ι x) = 0 := fun i x => h.z_X i x
  have xz : ∀ i x, Y.hT (ι x) (z i) = 0 := fun i x => by rw [hT_swap, zx, star_zero]
  have ex : ∀ i x, Y.hT (e i) (ι x) = 0 := fun i x => (h.hyp_X i x).1
  have xe : ∀ i x, Y.hT (ι x) (e i) = 0 := fun i x => by rw [hT_swap, ex, star_zero]
  have fx : ∀ i x, Y.hT (f i) (ι x) = 0 := fun i x => (h.hyp_X i x).2
  have xf : ∀ i x, Y.hT (ι x) (f i) = 0 := fun i x => by rw [hT_swap, fx, star_zero]
  have ez : ∀ i j, Y.hT (e i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).1
  have ze : ∀ i j, Y.hT (z j) (e i) = 0 := fun i x => by rw [hT_swap, ez, star_zero]
  have fz : ∀ i j, Y.hT (f i) (z j) = 0 := fun i x => (h.hyperbolicDecomp_hyp_orthogonal_line i x).2
  have zf : ∀ i j, Y.hT (z j) (f i) = 0 := fun i x => by rw [hT_swap, fz, star_zero]
  have ee : ∀ i j, Y.hT (e i) (e j) = 0 := fun i j => h.ee j i
  have ff : ∀ i j, Y.hT (f i) (f j) = 0 := fun i j => h.ff j i
  have fe : ∀ i j, Y.hT (f i) (e j) = if j = i then 1 else 0 := fun i j => h.ef j i
  have ef : ∀ i j, Y.hT (e i) (f j) = if i = j then 1 else 0 := fun i j => by
    rw [hT_swap, fe]; split_ifs <;> simp
  have xx : ∀ x y, Y.hT (ι x) (ι y) = X.hT x y := h.isom
  rw [sumMap_apply, sumMap_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, zz, zx, xz, ex, xe, fx, xf, ez, ze, fz, zf, ee, ff, fe, ef, xx, smul_eq_mul, mul_zero,
    Finset.sum_const_zero, add_zero, zero_add, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, mul_one, RingHom.id_apply, starRingEnd_apply]
  rw [add_comm (∑ i, star (p.2.2.1 i) * q.2.2.2 i)]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem sumMap_injective {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) : Function.Injective (sumMap Y X ι z e f) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  rintro ⟨x, α, β, γ⟩ hp
  have H := fun q => form_sumMap h (x, α, β, γ) q
  simp only [hp, map_zero, LinearMap.zero_apply] at H
  have h1 : x = 0 := X.nondeg.1 x fun y => by simpa using (H (y, 0, 0, 0)).symm
  have h2 : α = 0 := funext fun i => by
    simpa [Pi.single_apply, hc] using (H (0, Pi.single i 1, 0, 0)).symm
  have h3 : β = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, 0, Pi.single i 1)).symm
  have h4 : γ = 0 := funext fun i => by
    simpa [Pi.single_apply] using (H (0, 0, Pi.single i 1, 0)).symm
  simp [h1, h2, h3, h4]

def sumEquiv {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) :
    (X.V × (Fin a → D.host.E) × (Fin ρ → D.host.E) × (Fin ρ → D.host.E)) ≃ₗ[D.host.E] Y.V :=
  LinearEquiv.ofInjectiveOfFinrankEq (sumMap Y X ι z e f) (sumMap_injective h hc) (by
    simp only [Module.finrank_prod, Module.finrank_fin_fun, X.rank_eq, Y.rank_eq, h.rank]
    ring)

theorem sumEquiv_apply {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X ι z c e f) (hc : c ≠ 0) (p) :
    sumEquiv h hc p = sumMap Y X ι z e f p := rfl

theorem exists_isom {Y Y' X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {ι' : X.V →ₗ[D.host.E] Y'.V} {a ρ : ℕ}
    {z : Fin a → Y.V} {z' : Fin a → Y'.V} {c : D.host.E} {e f : Fin ρ → Y.V} {e' f' : Fin ρ → Y'.V}
    (h : IsDec Y X ι z c e f) (h' : IsDec Y' X ι' z' c e' f') (hc : c ≠ 0) :
    ∃ io : Y.V ≃ₗ[D.host.E] Y'.V, HSpace.IsIsomEmb Y Y' io.toLinearMap ∧
      (∀ x, io (ι x) = ι' x) ∧ (∀ i, io (z i) = z' i) ∧ ∀ i, io (e i) = e' i ∧ io (f i) = f' i := by
  have key : ∀ p, ((sumEquiv h hc).symm.trans (sumEquiv h' hc)) (sumMap Y X ι z e f p) =
      sumMap Y' X ι' z' e' f' p := fun p => by
    rw [← sumEquiv_apply h hc, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, sumEquiv_apply]
  refine ⟨(sumEquiv h hc).symm.trans (sumEquiv h' hc), fun x y => ?_, fun x => ?_, fun i => ?_, fun i => ⟨?_, ?_⟩⟩
  · obtain ⟨p, rfl⟩ := (sumEquiv h hc).surjective x
    obtain ⟨q, rfl⟩ := (sumEquiv h hc).surjective y
    rw [sumEquiv_apply, sumEquiv_apply, LinearEquiv.coe_coe, key, key, form_sumMap h, form_sumMap h']
  · simpa [sumMap_apply] using key (x, 0, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, Pi.single i 1, 0, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, Pi.single i 1, 0)
  · simpa [sumMap_apply, Pi.single_apply] using key (0, 0, 0, Pi.single i 1)

theorem isDec_rescale {Y X X' : HSp D} {ι : X'.V →ₗ[D.host.E] Y.V} {a ρ : ℕ} {z : Fin a → Y.V} {c : D.host.E}
    {e f : Fin ρ → Y.V} (h : IsDec Y X' ι z c e f) (φ : X.V →ₗ[D.host.E] X'.V) (hφ : HSpace.IsIsomEmb X X' φ)
    (hr : X.rank = X'.rank) (π : D.host.E) :
    IsDec Y X (ι ∘ₗ φ) (fun i => π • z i) (c * (π * star π)) e f := by
  refine
    { isom := fun x y => (h.isom _ _).trans (hφ x y)
      a_le := h.a_le
      rank := ?_
      z_norm := ?_
      z_X := ?_
      ee := h.ee
      ff := h.ff
      ef := h.ef
      hyp_X := fun i x => h.hyp_X i (φ x)
      hyperbolicDecomp_hyp_orthogonal_line := ?_ }
  · rw [hr, h.rank]
  · intro i
    have := h.z_norm i
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      starRingEnd_apply] at this ⊢
    rw [this]
    ring
  · intro i x
    have := h.z_X i (φ x)
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, LinearMap.comp_apply] at this ⊢
    rw [this, mul_zero]
  · intro i j
    have := h.hyperbolicDecomp_hyp_orthogonal_line i j
    simp only [HSpace.hD, LinearMap.map_smulₛₗ, smul_eq_mul] at this ⊢
    rw [this.1, this.2, mul_zero]
    exact ⟨rfl, rfl⟩

theorem stdIsomSt_of_rationalSt : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  intro D hR u
  refine ⟨?_, ?_⟩
  · obtain ⟨π, h1, h2, -⟩ := D.T_norm u
    exact ⟨π, h1, by rw [bridge_star_holds D.R D.host]; exact h2⟩
  intro π hπ s a ρ Y X ι z e f Y' X' ι' z' e' f' h h' hX hX' hp hp' hr
  obtain ⟨φ, hφ⟩ := hR X X' hX hX' hr fun τ => by rw [hp τ, hp' τ, hr]
  have h2 := isDec_rescale h' φ.toLinearMap hφ hr (π : D.host.E)
  rw [hπ.2] at h2
  have hc : ((s : ℤ) : D.host.E) * Tu D u ≠ 0 :=
    mul_ne_zero (Int.cast_ne_zero.mpr s.ne_zero) (Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero)
  obtain ⟨io, a1, a2, a3, a4⟩ := exists_isom h h2 hc
  exact ⟨φ, io, hφ, a1, a2, a3, a4⟩

end GlobalTheory.StdIsom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianStdIsometryOfRationalIsometryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RationalSt D → GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.StdIsomSt D := by
  first | exact @GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | exact GlobalTheory.StdIsom.stdIsomSt_of_rationalSt | (intros; apply GlobalTheory.StdIsom.stdIsomSt_of_rationalSt <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Lev Formalism.IndefR.Links
open Formalism.IndefR.Datum (IsSelfDualC)
open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.AdIsom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents
open GlobalTheory.StdFrames hiding OA
open GlobalTheory.IdemSupport (cP cO)
open GlobalTheory.NormSum.AdLattice (lat)

variable {D : D7}

theorem transportSt (D : D7) : TransportSt D := by
  intro W Y hr L Λ hL hΛ S hS n be be' h h'
  refine ⟨exists_transport W Y hr L Λ hL hΛ S hS n be be' h h', fun x hx x' => ?_⟩
  first
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' (selfDual_isFullLattice hL) h x hx x'
  | exact GlobalTheory.T.adelicIsometry_transport_unique_mod_stabilizer D W Y L Λ S hS n be be' hL.1 h x hx x'

private theorem fullLattice_of_glueVec {X : HSp D} {u : D.what₂.Word} {L₀ : Lat X}
    {f : Fin X.rank → EAf D} (hL : L₀.FG) (hf : IsGlueVec X u L₀ f) :
    Submodule.IsFullLattice D.host.E L₀ := by
  let β₀ : GL (Fin X.rank) (EAf D) := 1
  have hstd := GlobalTheory.NormSum.AdLattice.lat_isLattice β₀
  have hfull : Submodule.IsFullLattice D.host.E (L₀ ⊔ lat β₀) :=
    Submodule.IsFullLattice.of_le_of_fg _ le_sup_right (hL.sup hstd.fg)
  obtain ⟨β, hβ⟩ := exists_eq_lat hfull
  obtain ⟨β', hβ', -⟩ := exists_dual_frame X β
  have hle : L₀ ≤ lat β := hβ ▸ le_sup_left
  have := GlobalTheory.NormSum.AdLattice.lat_isLattice β'
  have := Submodule.IsLattice.of_fg D.host.E hL
  let t : D.host.Eˣ := Units.mk0 (Tu D u) (Tu_ne_zero u)
  refine Submodule.IsFullLattice.of_le D.host.E (M := t • lat β') ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  apply GlobalTheory.GlueUnique.mem_of_inc_mem_hat hL
  let xA : Fin X.rank → EAf D := fun i => inc D (x i)
  have hxA : ∀ z ∈ hat L₀, hA X z xA ∈ OA D :=
    fun z hz => (dual_hat_lat hβ' xA).2 (inc_mem_hat hx) z (hat_mono hle hz)
  obtain ⟨a, ha, hxa⟩ := hf.dual xA hxA
  have htx := add_mem_hat (smul_mem_hat (inc_Tu_mem u) hxa) (smul_mem_hat ha hf.mul_mem)
  rw [smul_sub, smul_comm (inc D (Tu D u)) a, sub_add_cancel] at htx
  convert htx using 1
  funext i
  change inc D (Tu D u * x i) = inc D (Tu D u) * inc D (x i)
  exact map_mul _ _ _

theorem gluedSt (D : D7) : GluedSt D := by
  intro u π hπ Y X ι z hz L₀ f₀ hb
  obtain ⟨f, hf, hff⟩ := GlobalTheory.T.exists_isAdelicGlueVector_of_glueBaseData D u π hπ X L₀ f₀ hb
  have hL₀ := fullLattice_of_glueVec hb.1.fg hf
  obtain ⟨x, hx⟩ := exists_sub_inc_mem_hat (D := D) (Λ := L₀) hL₀.span_eq_top f
  obtain ⟨x₀, hx₀⟩ := vA_surj X x
  rw [← hx₀] at hx
  have hg : IsGlueVec X u L₀ (vA X x₀) := hf.congr hx
  have hgl : IsGlued Y X ι z u π L₀ f₀ (glueLat Y X ι z u L₀ x₀) := by
    refine GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz L₀ x₀ f₀ hL₀.toIsLattice hg (fun w hw => ⟨?_, ?_⟩)
    · rw [← hff w hw, smul_smul, idem_mul_self]
    · rw [← hff w hw, ← smul_sub]
      exact smul_mem_hat (idem_mem w) hx
  have huniq : ∀ L, IsGlued Y X ι z u π L₀ f₀ L → L = glueLat Y X ι z u L₀ x₀ :=
    fun L hL => GlobalTheory.T.gluedHermitianLattice_unique D u π hπ Y X ι z L₀ f₀ L _ hL hgl
  refine ⟨⟨_, hgl, huniq⟩, fun L hL => ?_⟩
  rw [huniq L hL]
  exact GlobalTheory.T.gluedLattice_selfDual_primitive_meet D u Y X ι z hz L₀ x₀ hL₀ hg

theorem ungluedSt (D : D7) : UngluedSt D := by
  intro u π hπ Y X ι z hz L hSD hP
  obtain ⟨hlat, x₀, hL⟩ := GlobalTheory.T.primitive_lattice_glued_from_intersection D u Y X ι z hz L hSD hP

  have hg : IsGlueVec X u (capX Y X ι L) (vA X x₀) := by
    have key := GlobalTheory.T.isAdelicGlueVector_of_selfDual_primitive D u Y X ι z hz (capX Y X ι L) x₀ hlat
    rw [← hL] at key
    exact key hSD hP
  have := hlat
  refine ⟨fun w => idem w • vA X x₀,
    GlobalTheory.T.isGlueBaseData_of_isAdelicGlueVector D u π hπ X _ _ (by infer_instance) hg, ?_⟩
  have key := GlobalTheory.T.gluedLattice_prescribed_localComponents D u π Y X ι z hz (capX Y X ι L) x₀ (fun w => idem w • vA X x₀) hlat.toIsLattice hg
    (fun w _ => ⟨by simp only [smul_smul, idem_mul_self], by simp only [sub_self]; exact zero_mem_hat⟩)
  rwa [← hL] at key

theorem adelicIsometries (D : D7) : AdelicIsometries D := by
  unfold AdelicIsometries LamNSt
  exact ⟨plIdemSt D, transportSt D, GlobalTheory.T.correctionSt_of_transportSt D (transportSt D),
    splitGlueSt_of D (fun n Λ Λ' hΛ hΛ' v => GlobalTheory.T.localLattice_eq_iff_idempotent_components_over D n Λ Λ' hΛ hΛ' v),
    GlobalTheory.T.selfDualLattice_image_adelicUnitary D, GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D, GlobalTheory.T.hermitianStdIsometry_of_rationalIsometry D (GlobalTheory.T.hermitianSpaces_isometric_of_rank_signature D), GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof D,
    gluedSt D, ungluedSt D,
    ⟨fun u Y X ι z ρ e f h L hL nn hn => GlobalTheory.T.isSelfDualC_hyperbolicExtensionLattice_conjStable D u Y X ι z ρ e f h L hL nn hn,
      (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).1, (GlobalTheory.T.conjStable_inverseDifferent_and_normIdeal D).2⟩,
    frameSt D⟩

end GlobalTheory.AdIsom

end
