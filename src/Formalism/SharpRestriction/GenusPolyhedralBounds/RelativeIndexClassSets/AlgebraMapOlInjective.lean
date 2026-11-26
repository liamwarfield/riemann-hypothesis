module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ThetaLeMsupOfSetC
public import Formalism.GaussIdealIdentity.GaussIdealPrimality.GaussLocalizationLengthHolds
public import Formalism.FilteredPoleLength.LocalDescentLevels.LevelsChainOfAddOneLe
public import Formalism.FilteredPoleLength.LocalDescentLevels.LocalStepDescent

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

abbrev Idx (D : D7) (j N : ℕ) : Type := Fin (WeightFamilies.dimY D j + 1) × Fin N

abbrev Pol (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Type :=
  MvPolynomial (Idx D j N) (X.Ol la)

abbrev gI (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Ideal (Pol X la N) :=
  Formalism.DV.gaussIdeal (Idx D j N) (X.Ol la)

instance gI_isPrime (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : (gI X la N).IsPrime :=
  Formalism.DV.GaussP.gaussIdeal_isPrime _ _

def Op (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Type :=
  Localization.AtPrime (gI X la N)

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

instance Op.commRing : CommRing (Op X la N) := inferInstanceAs (CommRing (Localization.AtPrime (gI X la N)))
instance Op.isDomain : IsDomain (Op X la N) := Formalism.DV.GaussP.isDomain_A _ _
instance Op.isDVR : IsDiscreteValuationRing (Op X la N) := Formalism.DV.GaussP.isDVR _ _
instance Op.algPol : Algebra (Pol X la N) (Op X la N) :=
  inferInstanceAs (Algebra (Pol X la N) (Localization.AtPrime (gI X la N)))
instance Op.isLoc : IsLocalization.AtPrime (Op X la N) (gI X la N) :=
  inferInstanceAs (IsLocalization.AtPrime (Localization.AtPrime (gI X la N)) (gI X la N))
instance Op.algOl : Algebra (X.Ol la) (Op X la N) :=
  inferInstanceAs (Algebra (X.Ol la) (Localization.AtPrime (gI X la N)))
instance Op.towPol : IsScalarTower (X.Ol la) (Pol X la N) (Op X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Pol X la N) (Localization.AtPrime (gI X la N)))
instance Op.isLocalHom : IsLocalHom (algebraMap (X.Ol la) (Op X la N)) := Formalism.DV.GaussP.isLocalHom_A _ _

theorem Op.algebraMap_injective : Function.Injective (algebraMap (X.Ol la) (Op X la N)) :=
  Formalism.DV.GaussP.algebraMap_injective _ _

theorem Op.maximalIdeal_eq : IsLocalRing.maximalIdeal (Op X la N) =
    Ideal.map (algebraMap (X.Ol la) (Op X la N)) (IsLocalRing.maximalIdeal (X.Ol la)) :=
  Formalism.DV.GaussP.maximalIdeal_eq _ _

theorem Op.irreducible_map {ϖ : X.Ol la} (h : Irreducible ϖ) :
    Irreducible (algebraMap (X.Ol la) (Op X la N) ϖ) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, Op.maximalIdeal_eq, h.maximalIdeal_eq, Ideal.map_span,
    Set.image_singleton]

def Kp : Type := FractionRing (Op X la N)

instance Kp.field : Field (Kp X la N) := inferInstanceAs (Field (FractionRing (Op X la N)))
instance Kp.algOp : Algebra (Op X la N) (Kp X la N) :=
  inferInstanceAs (Algebra (Op X la N) (FractionRing (Op X la N)))
instance Kp.isFrac : IsFractionRing (Op X la N) (Kp X la N) :=
  inferInstanceAs (IsFractionRing (Op X la N) (FractionRing (Op X la N)))
instance Kp.algOl : Algebra (X.Ol la) (Kp X la N) :=
  ((@algebraMap (Op X la N) (Kp X la N) _ _ _).comp (algebraMap (X.Ol la) (Op X la N))).toAlgebra
instance Kp.towOp : IsScalarTower (X.Ol la) (Op X la N) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

theorem Kp.algebraMap_Ol_injective : Function.Injective (algebraMap (X.Ol la) (Kp X la N)) :=
  (IsFractionRing.injective (Op X la N) (Kp X la N)).comp (Op.algebraMap_injective X la N)

instance Kp.algKl : Algebra (X.Kl la) (Kp X la N) :=
  (IsFractionRing.lift (A := X.Ol la) (K := X.Kl la) (Kp.algebraMap_Ol_injective X la N)).toAlgebra
instance Kp.towKl : IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N) :=
  IsScalarTower.of_algebraMap_eq fun x =>
    (IsFractionRing.lift_algebraMap (A := X.Ol la) (K := X.Kl la) (Kp.algebraMap_Ol_injective X la N) x).symm

def Rp : Type := Kp X la N ⊗[X.Kl la] X.Vl la

instance Rp.commRing : CommRing (Rp X la N) := inferInstanceAs (CommRing (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algKp : Algebra (Kp X la N) (Rp X la N) :=
  inferInstanceAs (Algebra (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algOp : Algebra (Op X la N) (Rp X la N) :=
  inferInstanceAs (Algebra (Op X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOp : IsScalarTower (Op X la N) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (Op X la N) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algKl : Algebra (X.Kl la) (Rp X la N) :=
  inferInstanceAs (Algebra (X.Kl la) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towKl : IsScalarTower (X.Kl la) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Kl la) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.algOl : Algebra (X.Ol la) (Rp X la N) :=
  inferInstanceAs (Algebra (X.Ol la) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlKp : IsScalarTower (X.Ol la) (Kp X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Kp X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlOp : IsScalarTower (X.Ol la) (Op X la N) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (Op X la N) (Kp X la N ⊗[X.Kl la] X.Vl la))
instance Rp.towOlKl : IsScalarTower (X.Ol la) (X.Kl la) (Rp X la N) :=
  inferInstanceAs (IsScalarTower (X.Ol la) (X.Kl la) (Kp X la N ⊗[X.Kl la] X.Vl la))

def bcV : X.Vl la →ₐ[X.Kl la] Rp X la N :=
  (Algebra.TensorProduct.includeRight : X.Vl la →ₐ[X.Kl la] Kp X la N ⊗[X.Kl la] X.Vl la)

theorem bcV_isBaseChange : IsBaseChange (Kp X la N) (bcV X la N).toLinearMap :=
  TensorProduct.isBaseChange (X.Kl la) (X.Vl la) (Kp X la N)

def emb : X.Forms →+* Rp X la N :=
  (bcV X la N).toRingHom.comp (Algebra.TensorProduct.includeRight : X.Forms →ₐ[B.KO] X.Kl la ⊗[B.KO] X.Forms).toRingHom

theorem emb_apply (F : X.Forms) : emb X la N F =
    ((1 : Kp X la N) ⊗ₜ[X.Kl la] ((1 : X.Kl la) ⊗ₜ[B.KO] F) : Kp X la N ⊗[X.Kl la] X.Vl la) := rfl

theorem emb_eq_bcV (F : X.Forms) : emb X la N F = bcV X la N (X.bc la F) := rfl

def Vw (u : WeightFamilies.Wt D j) : Submodule (Kp X la N) (Rp X la N) :=
  Submodule.span (Kp X la N) (Set.range fun F : B.Cusp j u => emb X la N (X.inc u F))

theorem emb_mem_Vw (u : WeightFamilies.Wt D j) (F : B.Cusp j u) : emb X la N (X.inc u F) ∈ Vw X la N u :=
  Submodule.subset_span ⟨F, rfl⟩

theorem emb_smul (a : B.KO) (F : X.Forms) :
    emb X la N (a • F) = algebraMap B.KO (X.Kl la) a • emb X la N F := by
  rw [emb_eq_bcV, emb_eq_bcV, map_smul (X.bc la), ← algebraMap_smul (X.Kl la) a (X.bc la F), map_smul]

theorem Vw_eq_span_image (u : WeightFamilies.Wt D j) {s : Set (B.Cusp j u)} (hs : Submodule.span B.KO s = ⊤) :
    Vw X la N u = Submodule.span (Kp X la N) ((fun F : B.Cusp j u => emb X la N (X.inc u F)) '' s) := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono (Set.image_subset_range _ _))
  rintro _ ⟨F, rfl⟩
  have hF : F ∈ Submodule.span B.KO s := hs ▸ Submodule.mem_top
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => simp only [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    simp only [map_smul, emb_smul]
    rw [← algebraMap_smul (Kp X la N) (algebraMap B.KO (X.Kl la) a)]
    exact Submodule.smul_mem _ _ hx

theorem Vw_mul_le (u u' : WeightFamilies.Wt D j) : Vw X la N u * Vw X la N u' ≤ Vw X la N (wadd u u') := by
  unfold Vw
  rw [Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨F, rfl⟩, _, ⟨G, rfl⟩, rfl⟩
  obtain ⟨H, hH⟩ := X.inc_mul u u' F G
  exact ⟨H, by simp only [← hH, map_mul]⟩

theorem mul_mem_Vw {u u' : WeightFamilies.Wt D j} {x y : Rp X la N} (hx : x ∈ Vw X la N u) (hy : y ∈ Vw X la N u') :
    x * y ∈ Vw X la N (wadd u u') :=
  Vw_mul_le X la N u u' (Submodule.mul_mem_mul hx hy)

def Tv (p : Idx D j N) : Op X la N := algebraMap (Pol X la N) (Op X la N) (MvPolynomial.X p)

end

def addL (u wL : WeightFamilies.Wt D j) (n : ℕ) : WeightFamilies.Wt D j := wadd u (wsmul n wL)

theorem wadd_addL (u wL : WeightFamilies.Wt D j) (n : ℕ) : wadd wL (addL u wL n) = addL u wL (n + 1) := by
  unfold addL wadd wsmul
  simp only [WeightFamilies.Wt.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext τ i; ring
  · funext τ i; ring
  · ring

section
variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)

def sec (i : Fin (WeightFamilies.dimY D j + 1)) : Rp X la N :=
  ∑ k, (@algebraMap (Op X la N) (Kp X la N) _ _ _ (Tv X la N (i, k))) • emb X la N (X.inc wL (w k))

theorem sec_mem_Vw (i : Fin (WeightFamilies.dimY D j + 1)) : sec X la w i ∈ Vw X la N wL :=
  Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (emb_mem_Vw X la N wL (w k))

def secPow (α : Fin (WeightFamilies.dimY D j) → ℕ) : Rp X la N := ∏ i, sec X la w i.succ ^ α i

theorem sec_pow_mul_mem (i : Fin (WeightFamilies.dimY D j + 1)) (u : WeightFamilies.Wt D j) (n m : ℕ) {v : Rp X la N}
    (hv : v ∈ Vw X la N (addL u wL n)) : sec X la w i ^ m * v ∈ Vw X la N (addL u wL (n + m)) := by
  induction m with
  | zero => simpa using hv
  | succ m ih =>
    rw [pow_succ', mul_assoc, ← add_assoc, ← wadd_addL]
    exact mul_mem_Vw X la N (sec_mem_Vw X la w i) ih

def Mon (u : WeightFamilies.Wt D j) (a n : ℕ) : Submodule (Kp X la N) (Rp X la N) :=
  ⨆ (α : Fin (WeightFamilies.dimY D j) → ℕ) (_ : ∑ i, α i = a),
    (Vw X la N (addL u wL n)).map (LinearMap.mulLeft (Kp X la N) (secPow X la w α))

theorem sec_pow_mul_mem_Mon (u : WeightFamilies.Wt D j) (a n m : ℕ) {x : Rp X la N} (hx : x ∈ Mon X la w u a n) :
    sec X la w 0 ^ m * x ∈ Mon X la w u a (n + m) := by
  have h : Mon X la w u a n ≤
      (Mon X la w u a (n + m)).comap (LinearMap.mulLeft (Kp X la N) (sec X la w 0 ^ m)) := by
    refine iSup₂_le fun α hα => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro v hv
    show sec X la w 0 ^ m * (secPow X la w α * v) ∈ Mon X la w u a (n + m)
    rw [mul_left_comm]
    exact Submodule.mem_iSup_of_mem α (Submodule.mem_iSup_of_mem hα
      (Submodule.mem_map_of_mem (f := LinearMap.mulLeft (Kp X la N) (secPow X la w α))
        (sec_pow_mul_mem X la w 0 u n m hv)))
  exact h hx

def Fil (u : WeightFamilies.Wt D j) (a : ℕ) : Submodule (Kp X la N) (Rp X la N) where
  carrier := {f | f ∈ Vw X la N u ∧ ∃ k, a ≤ k ∧ sec X la w 0 ^ k * f ∈ Mon X la w u a (k - a)}
  zero_mem' := ⟨Submodule.zero_mem _, a, le_rfl, by rw [mul_zero]; exact Submodule.zero_mem _⟩
  add_mem' := by
    rintro f g ⟨hf, k, hk, hfk⟩ ⟨hg, k', hk', hgk⟩
    refine ⟨Submodule.add_mem _ hf hg, k + k', by omega, ?_⟩
    rw [mul_add]
    refine Submodule.add_mem _ ?_ ?_
    · have := sec_pow_mul_mem_Mon X la w u a (k - a) k' hfk
      rwa [← mul_assoc, ← pow_add, add_comm k' k, show k - a + k' = k + k' - a by omega] at this
    · have := sec_pow_mul_mem_Mon X la w u a (k' - a) k hgk
      rwa [← mul_assoc, ← pow_add, show k' - a + k = k + k' - a by omega] at this
  smul_mem' := by
    rintro c f ⟨hf, k, hk, hfk⟩
    exact ⟨Submodule.smul_mem _ c hf, k, hk, by rw [mul_smul_comm]; exact Submodule.smul_mem _ c hfk⟩

theorem mem_Fil {u : WeightFamilies.Wt D j} {a : ℕ} {f : Rp X la N} : f ∈ Fil X la w u a ↔
    f ∈ Vw X la N u ∧ ∃ k, a ≤ k ∧ sec X la w 0 ^ k * f ∈ Mon X la w u a (k - a) := Iff.rfl

end

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm
section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.QlenEqZeroOfLe
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

theorem finDim_of_isLat {O K V : Type} [CommRing O] [Field K] [Algebra O K] [AddCommGroup V] [Module K V]
    [Module O V] [IsScalarTower O K V] (M : Submodule O V) (h : Formalism.LatticeIndexTer.IsLat O K V M) :
    FiniteDimensional K V := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, ?_⟩⟩
  rw [← h.2, ← hS, Submodule.span_span_of_tower]

theorem qlen_inf_ne_top (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (M Θ : Submodule O V) (hM : Formalism.LatticeIndexTer.IsLat O K V M)
    (hΘ : Formalism.LatticeIndexTer.IsLat O K V Θ) (W : Submodule O V) :
    Formalism.LatticeIndexTer.qlen O V (M ⊓ W) (Θ ⊓ W) ≠ ⊤ := by
  have hfin := Formalism.LatticeIndexTer.latFinite O K V M Θ hM hΘ
  unfold Formalism.LatticeIndexTer.qlen at hfin ⊢
  let g : ↥(M ⊓ W) →ₗ[O] (↥M ⧸ Θ.comap M.subtype) :=
    (Θ.comap M.subtype).mkQ ∘ₗ Submodule.inclusion inf_le_left
  have hker : LinearMap.ker g = (Θ ⊓ W).comap (M ⊓ W).subtype := by
    ext ⟨y, hy⟩
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion, Submodule.mem_inf]
    exact ⟨fun h => ⟨h, hy.2⟩, fun h => h.1⟩
  have hle := Module.length_le_of_injective (g.ker.liftQ g le_rfl)
    (LinearMap.ker_eq_bot.1 (Submodule.ker_liftQ_eq_bot _ _ _ le_rfl))
  rw [hker] at hle
  exact ne_top_of_le_ne_top hfin hle

theorem length_comap_eq {O V W : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup W]
    [Module O W] (f : W →ₗ[O] V) (hf : Function.Injective f) (A B : Submodule O V)
    (hA : A ≤ LinearMap.range f) :
    Module.length O (↥(A.comap f) ⧸ (B.comap f).comap (A.comap f).subtype) =
      Module.length O (↥A ⧸ B.comap A.subtype) := by
  let g0 : ↥(A.comap f) →ₗ[O] ↥A := f.restrict (fun x hx => hx)
  have hg : Function.Bijective g0 := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply hf
      exact congrArg Subtype.val hxy
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hA hy
      exact ⟨⟨x, hy⟩, rfl⟩
  let g : ↥(A.comap f) ≃ₗ[O] ↥A := LinearEquiv.ofBijective g0 hg
  refine (Submodule.Quotient.equiv _ _ g ?_).length_eq
  ext ⟨y, hy⟩
  constructor
  · rintro ⟨⟨x, hx⟩, hxB, hxy⟩
    have : f x = y := congrArg Subtype.val hxy
    simpa [← this] using hxB
  · intro hyB
    obtain ⟨x, rfl⟩ := hA hy
    exact ⟨⟨x, hy⟩, hyB, rfl⟩

theorem qlen_eq_zero_of_le {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (A B : Submodule O V)
    (h : B ≤ A) : Formalism.LatticeIndexTer.qlen O V B A = 0 := by
  unfold Formalism.LatticeIndexTer.qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  induction a using Submodule.Quotient.induction_on with
  | _ x =>
    induction b using Submodule.Quotient.induction_on with
    | _ y => exact (Submodule.Quotient.eq _).2 (h (x - y).2)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem qlen_eq_inW (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (la : HeightOneSpectrum (𝓞 B.KO))
    (N N' : Submodule (X.Ol la) (X.Vl la)) (V' : Submodule (X.Kl la) (X.Vl la))
    (hV' : V' ≤ WL X ka la) :
    Formalism.LatticeIndexTer.qlen (X.Ol la) ↥(WL X ka la)
              (inW X ka la N ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
              (inW X ka la N' ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la)) =
      X.qlen la (N ⊓ X.ofK la V') (N' ⊓ X.ofK la V') := by
  refine length_comap_eq ((WL X ka la).subtype.restrictScalars (X.Ol la)) ?_ (N ⊓ X.ofK la V')
    (N' ⊓ X.ofK la V') ?_
  · exact Subtype.val_injective
  · intro x hx
    exact ⟨⟨x, hV' hx.2⟩, rfl⟩

end Formalism.MainNotions.Gaps.T0
end
end

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.T0

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    0 ≤ X.phiC la y := by
  unfold PJ.phiC
  split_ifs with h
  · refine mul_nonneg (Nat.cast_nonneg _) ?_
    unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
    refine Real.sInf_nonneg ?_
    rintro x ⟨l, -, h2, rfl⟩
    by_cases hb : (P.loc X.dat (resCh la)).beS (X.pt66 la y) = 0
    · rw [hb]; simp
    · refine (h2 _ ?_ hb).le
      intro a
      by_cases ha : a = 0
      · subst ha; simp
      · exact ((P.loc X.dat (resCh la)).be_pos (X.pt66 la y) a ha).le
  · exact le_rfl

namespace LocDat

variable {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {la : HeightOneSpectrum (𝓞 B.KO)} (L : LocDat X ka la)

variable {L}

end LocDat

end Formalism.MainNotions.Gaps.T0
end
end
