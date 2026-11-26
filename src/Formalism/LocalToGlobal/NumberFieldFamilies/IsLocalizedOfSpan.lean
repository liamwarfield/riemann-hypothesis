module

public import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
public import Formalism.LocalToGlobal.UnitaryNorms.CharGal

@[expose] public section

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Module

namespace Formalism.L2.Fam.NPC.LatticeFinitenessFree

open Formalism.L2.Fam.NPC

theorem span_top_of_image {L : Type*} [Field L] (e : L →+* ℂ) {M V : Type*} [AddCommGroup M] [Module L M] [AddCommGroup V]
    [Module ℂ V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M) (hb1 : LinearIndependent ℂ (fun k => jm (b k)))
    (hb2 : Submodule.span ℂ (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span ℂ (jm '' S) = ⊤) :
    Submodule.span L S = ⊤ := by
  by_contra hW
  obtain ⟨f, hf0, hfW⟩ := Submodule.exists_le_ker_of_lt_top (Submodule.span L S) (lt_top_iff_ne_top.2 hW)
  let bC : Module.Basis ι ℂ V := Module.Basis.mk hb1 (le_of_eq hb2.symm)
  let F : V →ₗ[ℂ] ℂ := bC.constr ℂ fun k => e (f (b k))
  have hFb : ∀ k, F (jm (b k)) = e (f (b k)) := fun k => by
    have h : jm (b k) = bC k := (Module.Basis.mk_apply hb1 (le_of_eq hb2.symm) k).symm
    rw [h, Module.Basis.constr_basis]
  have hFj : ∀ x, F (jm x) = e (f x) := by
    intro x
    have hx : x ∈ Submodule.span L (Set.range b) := b.span_eq ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => obtain ⟨k, rfl⟩ := hy; exact hFb k
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), map_add (f := _), hy, hz, map_add (f := _), map_add (f := _)]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, map_smul, hy, map_smul, smul_eq_mul, smul_eq_mul, map_mul]
  have hF0 : F = 0 := by
    refine LinearMap.ext fun v => ?_
    have hv : v ∈ Submodule.span ℂ (jm '' S) := hS ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hFj, show f x = 0 from hfW (Submodule.subset_span hx), map_zero]; rfl
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  apply hf0
  refine LinearMap.ext fun x => e.injective ?_
  rw [← hFj, hF0]
  simp

section Loc

variable {O : Type*} [CommRing O] [IsDomain O] {K : Type*} [Field K] [Algebra O K] [IsFractionRing O K]
  {P : Type*} [AddCommGroup P] [Module K P] [Module O P] [IsScalarTower O K P]

theorem isLocalized_of_span (N : Submodule O P) (hN : Submodule.span K (N : Set P) = ⊤) :
    IsLocalizedModule (nonZeroDivisors O) N.subtype := by
  have hK : ∀ s ∈ nonZeroDivisors O, algebraMap O K s ≠ 0 := fun s hs =>
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 (nonZeroDivisors.ne_zero hs)
  refine ⟨fun s => ?_, fun y => ?_, fun {a b} h => ⟨1, by simpa using Subtype.ext h⟩⟩
  · rw [Module.End.isUnit_iff]
    have hs := hK s s.2
    refine ⟨fun x y hxy => ?_, fun y => ⟨(algebraMap O K s)⁻¹ • y, ?_⟩⟩
    · have h1 : (algebraMap O K s) • x = (algebraMap O K s) • y := by
        simpa [algebraMap_smul] using hxy
      exact (smul_right_injective P hs) h1
    · show (s : O) • ((algebraMap O K s)⁻¹ • y) = y
      rw [← algebraMap_smul K (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]
  · have hy : y ∈ Submodule.span K (N : Set P) := hN ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact ⟨⟨⟨x, hx⟩, 1⟩, by simp⟩
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨⟨b, t⟩, hb⟩ := hy
      refine ⟨⟨(t : O) • a + (s : O) • b, s * t⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul] at ha hb ⊢
      rw [← ha, ← hb, Submonoid.coe_mul, smul_add, mul_smul, mul_smul, smul_comm (t : O) (s : O) x]
    | smul c x _ hx =>
      obtain ⟨⟨a, s⟩, ha⟩ := hx
      obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := O) c
      refine ⟨⟨n • a, ⟨d, hd⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submodule.subtype_apply, Submodule.coe_smul] at ha ⊢
      rw [← ha, Submonoid.coe_mul, mul_smul]
      change (d : O) • (s : O) • ((algebraMap O K n / algebraMap O K d) • x) = n • (s : O) • x
      rw [← algebraMap_smul K (d : O), ← algebraMap_smul K (s : O), ← algebraMap_smul K n, ← algebraMap_smul K (s : O) x,
        smul_smul, smul_smul, smul_smul]
      congr 1
      have hd0 : algebraMap O K d ≠ 0 := hK d hd
      field_simp

end Loc

theorem span_image_top {L : Type*} [Field L] {K : Type*} [Field K] (e : L →+* K) {M V : Type*} [AddCommGroup M] [Module L M]
    [AddCommGroup V] [Module K V] (jm : M →ₛₗ[e] V) {ι : Type*} (b : Module.Basis ι L M)
    (hb2 : Submodule.span K (Set.range fun k => jm (b k)) = ⊤) (S : Set M) (hS : Submodule.span L S = ⊤) :
    Submodule.span K (jm '' S) = ⊤ := by
  refine le_antisymm le_top (hb2 ▸ Submodule.span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  have key : ∀ x ∈ Submodule.span L S, jm x ∈ Submodule.span K (jm '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hx
  exact key _ (hS ▸ Submodule.mem_top)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂}

theorem span_latL (i : LocT B) : Submodule.span what₂.LL (latL B i) = ⊤ := by
  have hb := what₂.jMt_basis (what₂.muTw (wOf B i)) (jOf B i) (Module.Free.chooseBasis what₂.LL _)
  refine span_top_of_image what₂.embLL (what₂.jMt (what₂.muTw (wOf B i)) (jOf B i)) _ hb.1 hb.2 _ ?_
  have h := (what₂.MtLat (what₂.muTw (wOf B i)) (jOf B i)).span_top
  refine le_antisymm le_top (h ▸ Submodule.span_mono fun v hv => ?_)
  obtain ⟨x, rfl⟩ := what₂.MtLat_sub _ _ v hv
  exact ⟨x, hv, rfl⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem span_mtSub (hC : PartCompl B) (i : LocT B) :
    Submodule.span (FractionRing (OOf B i)) ((MtSub B hC i : Submodule (OOf B i) (partOf B i)) : Set (partOf B i)) = ⊤ := by
  have hV := span_image_top (B.ec (jOf B i) (wOf B i)) (B.iV (jOf B i) (wOf B i)) (Module.Free.chooseBasis what₂.LL _)
    (B.iV_basis (jOf B i) (wOf B i) _).2 _ (span_latL i)
  refine le_antisymm le_top ?_
  rintro y -
  obtain ⟨x, rfl⟩ := Submodule.projectionOnto_surjective (hC i) y
  have hx : x ∈ Submodule.span (FractionRing (OOf B i)) (B.iV (jOf B i) (wOf B i) '' latL B i) := hV ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, rfl⟩ := hz
    exact Submodule.subset_span (Submodule.subset_span ⟨u, hu, rfl⟩)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ _ ha


set_option synthInstance.maxHeartbeats 400000 in
theorem mtLoc_holds (hC : PartCompl B) : MtLoc B hC := fun i => isLocalized_of_span _ (span_mtSub hC i)

end Formalism.L2.Fam.NPC.LatticeFinitenessFree
end
end

section -- merged from Formalism.LocalToGlobal.NumberFieldFamilies.RamifiedPrimesTrivialTuple
section -- merged from Formalism.LocalToGlobal.UnitaryNorms.UnrAEPf
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

theorem eq_one_of_pow_near {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hre : ∀ n : ℕ, 1 / 2 < (z ^ n).re := fun n => by
    have h1 := h n
    have h2 : |(z ^ n - 1).re| ≤ ‖z ^ n - 1‖ := Complex.abs_re_le_norm _
    rw [Complex.sub_re, Complex.one_re] at h2
    have h3 := (abs_lt.mp (lt_of_le_of_lt h2 h1)).1
    linarith
  have hsum_re : (N : ℝ) * (1 / 2) ≤ (∑ i ∈ Finset.range N, z ^ i).re := by
    rw [Complex.re_sum]
    have h4 : ∑ i ∈ Finset.range N, (1 / 2 : ℝ) ≤ ∑ i ∈ Finset.range N, (z ^ i).re :=
      Finset.sum_le_sum fun i _ => (hre i).le
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h4
    exact h4
  have hsum_norm : ‖∑ i ∈ Finset.range N, z ^ i‖ < 1 / 2 / ‖z - 1‖ := by
    rw [geom_sum_eq hz, norm_div]
    exact div_lt_div_of_pos_right (h N) hpos
  have h5 := (hsum_re.trans (Complex.re_le_norm _)).trans_lt hsum_norm
  have h6 : (1 : ℝ) / 2 / ‖z - 1‖ = (1 / ‖z - 1‖) * (1 / 2) := by ring
  rw [h6] at h5
  have h7 : (1 / ‖z - 1‖) * (1 / 2) < (N : ℝ) * (1 / 2) := by linarith
  linarith

variable {L : Type} [Field L] [NumberField L]

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 L)) : IsOpen ((v.adicCompletionIntegers L : Set (v.adicCompletion L))) :=
  Valued.isOpen_valuationSubring _

theorem finiteSingle_mem (Vf : Set (FiniteAdeleRing (𝓞 L) L)) (hV : Vf ∈ nhds (1 : FiniteAdeleRing (𝓞 L) L)) :
    ∃ S : Set (HeightOneSpectrum (𝓞 L)), S.Finite ∧ ∀ v, v ∉ S → ∀ y : v.adicCompletion L,
      y ∈ v.adicCompletionIntegers L → finiteSingle L v y ∈ Vf := by
  classical
  have hσ := RestrictedProduct.isOpenEmbedding_structureMap (R := fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
    (A := fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) isOpen_integers
  have h1 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite 1 = 1 :=
    RestrictedProduct.ext _ _ fun i => rfl
  have h2 : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite ⁻¹' Vf ∈ nhds 1 := by
    apply hσ.continuous.continuousAt.preimage_mem_nhds
    rw [h1]
    exact hV
  rw [nhds_pi, Filter.mem_pi] at h2
  obtain ⟨I, hI, t, ht, hsub⟩ := h2
  refine ⟨I, hI, fun v hv y hy => ?_⟩
  have hmem : (Pi.mulSingle v (⟨y, hy⟩ : ((v.adicCompletionIntegers L : Set (v.adicCompletion L)))) :
      (i : HeightOneSpectrum (𝓞 L)) → ((i.adicCompletionIntegers L : Set (i.adicCompletion L)))) ∈ I.pi t := by
    intro i hi
    have hne : i ≠ v := fun e => hv (e ▸ hi)
    rw [Pi.mulSingle_eq_of_ne hne]
    exact mem_of_mem_nhds (ht i)
  have hg := hsub hmem
  have e : RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 L) => v.adicCompletion L)
      (fun v => (v.adicCompletionIntegers L : Set (v.adicCompletion L))) Filter.cofinite (Pi.mulSingle v ⟨y, hy⟩) =
      finiteSingle L v y := by
    apply RestrictedProduct.ext
    intro i
    rw [RestrictedProduct.structureMap_apply]
    show _ = Pi.mulSingle v y i
    by_cases hi : i = v
    · subst hi
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne hi, Pi.mulSingle_eq_of_ne hi]
      rfl
  rw [← e]
  exact hg

theorem mem_integers_of_isUnitAt {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) :
    (x : v.adicCompletion L) ∈ v.adicCompletionIntegers L := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact hx.le

theorem isUnitAt_inv {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) : IsUnitAt v x⁻¹ := by
  unfold IsUnitAt at *
  rw [Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]

theorem isUnitAt_pow {v : HeightOneSpectrum (𝓞 L)} {x : (v.adicCompletion L)ˣ} (hx : IsUnitAt v x) (n : ℕ) :
    IsUnitAt v (x ^ n) := by
  unfold IsUnitAt at *
  rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]

theorem unrAE (L : Type) [Field L] [NumberField L] : UnrAE L := by
  intro χ hχ
  set U : Set (Ideles L) := {a | ‖((χ a : ℂˣ) : ℂ) - 1‖ < 1 / 2} with hUdef
  have hUo : IsOpen U :=
    isOpen_lt ((Units.continuous_val.comp hχ).sub continuous_const).norm continuous_const
  have hU1 : (1 : Ideles L) ∈ U := by
    show ‖((χ 1 : ℂˣ) : ℂ) - 1‖ < 1 / 2
    rw [map_one, Units.val_one, sub_self, norm_zero]
    norm_num
  obtain ⟨W, hWo, hWU⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hUo
  have hW1 : Units.embedProduct _ (1 : Ideles L) ∈ W := by
    rw [← Set.mem_preimage, hWU]
    exact hU1
  rw [map_one] at hW1
  obtain ⟨W1, hW1n, W2, hW2n, hprod⟩ := mem_nhds_prod_iff.mp (hWo.mem_nhds hW1)
  have hW2' : MulOpposite.op ⁻¹' W2 ∈ nhds (1 : AdeleRing (𝓞 L) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hW2n
  have hV : W1 ∩ MulOpposite.op ⁻¹' W2 ∈ nhds ((1 : InfiniteAdeleRing L), (1 : FiniteAdeleRing (𝓞 L) L)) :=
    Filter.inter_mem hW1n hW2'
  obtain ⟨Vi, hVi, Vf, hVf, hVprod⟩ := mem_nhds_prod_iff.mp hV
  obtain ⟨S, hS, hSV⟩ := finiteSingle_mem Vf hVf
  have key : ∀ v, v ∉ S → ∀ x : (v.adicCompletion L)ˣ, IsUnitAt v x → localIdele L v x ∈ U := by
    intro v hv x hx
    have hin : ∀ y : (v.adicCompletion L)ˣ, IsUnitAt v y →
        ((localIdele L v y : Ideles L) : AdeleRing (𝓞 L) L) ∈ W1 ∩ MulOpposite.op ⁻¹' W2 := fun y hy =>
      hVprod ⟨mem_of_mem_nhds hVi, hSV v hv _ (mem_integers_of_isUnitAt hy)⟩
    have h1 := hin x hx
    have h2 := hin x⁻¹ (isUnitAt_inv hx)
    rw [← hWU, Set.mem_preimage, Units.embedProduct_apply]
    refine hprod ⟨h1.1, ?_⟩
    have h3 := h2.2
    rw [map_inv] at h3
    exact h3
  refine (hS.subset ?_ : {v | ¬ _}.Finite)
  intro v hv
  by_contra hvS
  apply hv
  intro x hx
  have hpow : ∀ n : ℕ, ‖((χ (localIdele L v x) : ℂˣ) : ℂ) ^ n - 1‖ < 1 / 2 := fun n => by
    have h' : ‖((χ (localIdele L v (x ^ n)) : ℂˣ) : ℂ) - 1‖ < 1 / 2 := key v hvS (x ^ n) (isUnitAt_pow hx n)
    rwa [map_pow, map_pow, Units.val_pow_eq_pow_val] at h'
  exact Units.ext (eq_one_of_pow_near hpow)

end Formalism.L2.Host
end
end

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Fam.DivCQ

open Formalism.BasicNotions Formalism.L2.Host

variable {D : D7} {C : CharFrame D} {nch : NChoice D}

theorem unrAt_one {L : Type} [Field L] [NumberField L] (w : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).UnrAt w :=
  fun _ _ => rfl

structure ConjAt (D : D7) where
  M : ℕ → Type
  [instM : ∀ j, NormedAddCommGroup (M j)]
  [instMi : ∀ j, InnerProductSpace ℂ (M j)]
  [instMf : ∀ j, FiniteDimensional ℂ (M j)]
  T : ℕ → Type
  [instT : ∀ j, NormedAddCommGroup (T j)]
  [instTi : ∀ j, InnerProductSpace ℂ (T j)]
  [instTf : ∀ j, FiniteDimensional ℂ (T j)]
  th : ∀ j, T j →ₗ[ℂ] M j
  part : ∀ j, D.what₂.FT → Submodule ℂ (M j)

attribute [instance] ConjAt.instM ConjAt.instMi ConjAt.instMf ConjAt.instT ConjAt.instTi ConjAt.instTf


end Formalism.L2.Fam.DivCQ

end
end
