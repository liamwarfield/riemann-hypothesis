module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SecondProjectionOrthogonalComplement

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.MemOfProjTwoEqZero
namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

variable {E : Type} [Field E] [NumberField E]

section PT

variable (X : PT E) (I : Submodule ℤ (Vsp X.dim))

def Ip : Submodule ℤ (Vsp X.dim) where
  carrier := {x | x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0}
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨X.L.add_mem hx hy, fun a ha => ?_⟩
    rw [Hf_add_l, Complex.add_im, hx' a ha, hy' a ha, add_zero]
  zero_mem' := ⟨X.L.zero_mem, fun a _ => by simp [Hf]⟩
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    refine ⟨X.L.smul_mem c hx, fun a ha => ?_⟩
    rw [← Int.cast_smul_eq_zsmul ℂ c x, Hf_smul_l, Complex.mul_im, hx' a ha]
    simp

theorem mem_Ip {x : Vsp X.dim} : x ∈ Ip X I ↔ x ∈ X.L ∧ ∀ a ∈ I, (Hf x a).im = 0 := Iff.rfl

variable {X I}

theorem iso_IR (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) :
    ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 :=
  Hf_im_span_iso (I : Set (Vsp X.dim)) hiso

theorem isU_uc (x : Vsp X.dim) : IsU I x (uc (IR I) x) :=
  ⟨uc_mem _ x, fun a ha => inner_uc _ x a ha⟩

theorem z_im_Ip {x : Vsp X.dim} (hx : x ∈ Ip X I) (k : Fin (dK (IR I))) : (z (IR I) k x).im = 0 :=
  Hf_im_span_right (I : Set (Vsp X.dim)) x (fun a ha => hx.2 a ha) _ (e_mem _ k)

theorem uc_Ip {x : Vsp X.dim} (hx : x ∈ Ip X I) : uc (IR I) x = 0 := by
  simp [uc, z_im_Ip hx]

theorem proj_one_mem_realSpan {x : Vsp X.dim} (hx : x ∈ Ip X I) : p1 (IR I) x ∈ IR I := by
  refine Submodule.sum_mem _ fun k _ => ?_
  have : z (IR I) k x = ((z (IR I) k x).re : ℂ) := by
    apply Complex.ext <;> simp [z_im_Ip hx]
  rw [this, Complex.coe_smul]
  exact Submodule.smul_mem _ _ (e_mem _ k)

theorem uc_sub (x y : Vsp X.dim) : uc (IR I) (x - y) = uc (IR I) x - uc (IR I) y := by
  simp [uc, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]

theorem uc_add (x y : Vsp X.dim) : uc (IR I) (x + y) = uc (IR I) x + uc (IR I) y := by
  simp [uc, z, Hf_add_l, add_smul, Finset.sum_add_distrib]

theorem proj_two_sub (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x - y) = p2 K x - p2 K y := by
  simp only [p2, p1, z, Hf_sub_l, sub_smul, Finset.sum_sub_distrib]; abel

theorem proj_two_add (K : Submodule ℝ (Vsp X.dim)) (x y : Vsp X.dim) : p2 K (x + y) = p2 K x + p2 K y := by
  simp only [p2, p1, z, Hf_add_l, add_smul, Finset.sum_add_distrib]; abel

theorem norm_uc_le (hiso : ∀ x ∈ I, ∀ y ∈ I, (Hf x y).im = 0) (v : Vsp X.dim) :
    ‖uc (IR I) v‖ ≤ ‖v‖ := by
  have hK := iso_IR hiso
  have h1 : ‖uc (IR I) v‖ ^ 2 = ∑ k, (z (IR I) k v).im ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_uc _ v _ (uc_mem _ v), uc, Hf_sum_r, Complex.im_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Hf_rsmul_r, Complex.im_ofReal_mul, z]; ring
  have h2 := norm_sq_decomp hK v
  have h3 : ∑ k, (z (IR I) k v).im ^ 2 ≤ ∑ k, ‖z (IR I) k v‖ ^ 2 :=
    Finset.sum_le_sum fun k _ => by
      rw [sq_le_sq, abs_norm]; exact Complex.abs_im_le_norm _
  have h4 : 0 ≤ ‖p2 (IR I) v‖ ^ 2 := sq_nonneg _
  nlinarith [norm_nonneg (uc (IR I) v), norm_nonneg v]

end PT

section Split

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}

theorem th_pos (P : Par X DF) : 0 < P.th := by
  have hf : (1 : ℝ) ≤ PT.f E := by
    have := P.hfr
    have : 1 ≤ PT.f E := by
      rcases Nat.eq_zero_or_pos (PT.f E) with h | h
      · rw [h] at this; simp at this
      · exact h
    exact_mod_cast this
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  simp only [Par.th, th]
  apply Real.sqrt_pos.2
  apply div_pos _ hq
  have : 0 < P.R0 ^ 2 := by linarith
  positivity

theorem proj_one_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p1 K a = a := by
  have hrep := (ob K).sum_repr ⟨a, ha⟩
  have ha' : a = ∑ k, ((ob K).repr ⟨a, ha⟩ k) • e K k := by
    have := congrArg Subtype.val hrep
    simpa [e] using this.symm
  have hz : ∀ k, z K k a = ((ob K).repr ⟨a, ha⟩ k : ℂ) := by
    intro k
    conv_lhs => rw [ha']
    simp only [z, Hf_sum_l, Hf_rsmul_l, Hf_e hK, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  conv_rhs => rw [ha']
  simp only [p1, hz, Complex.coe_smul]

theorem proj_two_of_mem {K : Submodule ℝ (Vsp X.dim)} (hK : ∀ a ∈ K, ∀ b ∈ K, (Hf a b).im = 0)
    {a : Vsp X.dim} (ha : a ∈ K) : p2 K a = 0 := by
  rw [p2, proj_one_of_mem hK ha, sub_self]

variable (hI : IsSplit P I)
include hI

theorem hK_of : ∀ a ∈ IR I, ∀ b ∈ IR I, (Hf a b).im = 0 := iso_IR hI.iso

theorem gap_le_norm_proj_two {x : Vsp X.dim} (hx : x ∈ Ip X I) (hxI : x ∉ I) : P.th ≤ ‖p2 (IR I) x‖ := by
  have h := hI.thick x hx.1 hx.2 hxI
  refine h.trans ?_
  have := Metric.infDist_le_dist_of_mem (x := x) (proj_one_mem_realSpan hx)
  rw [dist_eq_norm] at this
  simpa [p2] using this

theorem mem_of_proj_two_eq_zero {x : Vsp X.dim} (hx : x ∈ Ip X I) (h0 : p2 (IR I) x = 0) : x ∈ I := by
  by_contra hxI
  have h1 := gap_le_norm_proj_two hI hx hxI
  rw [h0, norm_zero] at h1
  exact absurd h1 (not_le.2 (th_pos P))

theorem herm_im_proj_two {x y : Vsp X.dim} (hx : x ∈ Ip X I) (hy : y ∈ Ip X I) :
    (Hf (p2 (IR I) x) (p2 (IR I) y)).im = (Hf x y).im := by
  rw [Hf_decomp (hK_of hI) x y, Complex.add_im, Complex.im_sum]
  have : ∑ k, (z (IR I) k x * (starRingEnd ℂ) (z (IR I) k y)).im = 0 :=
    Finset.sum_eq_zero fun k _ => by
      rw [Complex.mul_im, Complex.conj_re, Complex.conj_im, z_im_Ip hx, z_im_Ip hy]; ring
  rw [this, zero_add]

theorem sign_eq_of_proj_two_eq {x y : Vsp X.dim} (hx : x ∈ Ip X I) (hy : y ∈ Ip X I)
    (h : p2 (IR I) x = p2 (IR I) y) : X.eps x = X.eps y := by
  have hd : x - y ∈ Ip X I := (Ip X I).sub_mem hx hy
  have hdI : x - y ∈ I := mem_of_proj_two_eq_zero hI hd (by rw [proj_two_sub, h, sub_self])
  have h1 := X.eps_add y hy.1 (x - y) (X.L.sub_mem hx.1 hy.1)
  rw [add_sub_cancel, hI.eps _ hdI, hy.2 _ hdI] at h1
  simp at h1
  exact_mod_cast h1

end Split

section Lat

theorem pack_K {ι : Type} [Fintype ι] (hP : Ext.PackingCount) (K : Submodule ℝ (EuclideanSpace ℂ ι))
    (S : Finset (EuclideanSpace ℂ ι)) (hS : ∀ u ∈ S, u ∈ K) (δ R : ℝ) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hR : ∀ u ∈ S, ‖u‖ ≤ R) (hsep : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → δ ≤ dist u v) :
    (S.card : ℝ) ≤ (3 * R / δ) ^ (dK K) := by
  classical
  let f : EuclideanSpace ℂ ι → EuclideanSpace ℝ (Fin (dK K)) :=
    fun u => if h : u ∈ K then (ob K).repr ⟨u, h⟩ else 0
  have hf : ∀ u (h : u ∈ K), f u = (ob K).repr ⟨u, h⟩ := fun u h => by simp [f, h]
  have hinj : Set.InjOn f S := by
    intro u hu v hv huv
    rw [hf u (hS u hu), hf v (hS v hv)] at huv
    exact congrArg Subtype.val ((ob K).repr.injective huv)
  have hcard := Finset.card_image_of_injOn hinj
  rw [← hcard]
  apply hP (dK K) (S.image f) δ R hδ hδR
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    rw [hf u (hS u hu), LinearIsometryEquiv.norm_map]
    exact hR u hu
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
    have huv : u ≠ v := fun h => hxy (by rw [h])
    rw [hf u (hS u hu), hf v (hS v hv), LinearIsometryEquiv.dist_map]
    exact hsep u hu v hv huv

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF}

theorem cutoff_pos (P : Par X DF) : 0 < b0 (E := E) P.q P.R0 := by
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hRR : 0 < RR (E := E) := by simp only [RR]; have := P.hrd; positivity
  have hR0 := P.hR0.1
  have : 0 < P.R0 ^ 2 := by linarith
  simp only [b0]; positivity

variable (hI : IsSplit P I)
include hI

theorem uc_sep {y y' : Vsp X.dim} (hy : y ∈ X.L) (hy' : y' ∈ X.L)
    (hne : uc (IR I) y ≠ uc (IR I) y') :
    Real.sqrt (b0 (E := E) P.q P.R0) ≤ dist (uc (IR I) y) (uc (IR I) y') := by
  rw [dist_eq_norm, ← uc_sub]
  have hu := isU_uc (I := I) (y - y')
  have h0 : uc (IR I) (y - y') ≠ 0 := by rw [uc_sub]; exact sub_ne_zero.2 hne
  have := hI.sep _ (X.L.sub_mem hy hy') _ hu h0
  calc Real.sqrt (b0 (E := E) P.q P.R0) ≤ Real.sqrt (‖uc (IR I) (y - y')‖ ^ 2) := Real.sqrt_le_sqrt this
    _ = _ := Real.sqrt_sq (norm_nonneg _)

theorem reps_bdd (hP : Ext.PackingCount) (C : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ y ∈ X.L, ‖uc (IR I) y‖ ≤ C →
      ∃ y' ∈ X.L, uc (IR I) y' = uc (IR I) y ∧ ‖p2 (IR I) y'‖ ≤ M := by
  classical
  set F : Set (Vsp X.dim) := {u | ∃ y ∈ X.L, ‖uc (IR I) y‖ ≤ C ∧ uc (IR I) y = u} with hF
  have hb := cutoff_pos P
  set δ := Real.sqrt (b0 (E := E) P.q P.R0)
  have hδ : 0 < δ := Real.sqrt_pos.2 hb
  have hfin : F.Finite := by
    by_contra hinf
    set R := max C δ
    obtain ⟨N, hN⟩ := exists_nat_gt ((3 * R / δ) ^ (dK (IR I)))
    obtain ⟨T, hTF, hTc⟩ := Set.Infinite.exists_subset_card_eq hinf N
    have := pack_K hP (IR I) T (fun u hu => by
        obtain ⟨y, -, -, rfl⟩ := hTF hu; exact uc_mem _ y) δ R hδ (le_max_right _ _)
      (fun u hu => by obtain ⟨y, -, hyC, rfl⟩ := hTF hu; exact hyC.trans (le_max_left _ _))
      (fun u hu v hv huv => by
        obtain ⟨y, hy, -, rfl⟩ := hTF hu
        obtain ⟨y', hy', -, rfl⟩ := hTF hv
        exact uc_sep hI hy hy' huv)
    rw [hTc] at this
    linarith
  let g : Vsp X.dim → Vsp X.dim := fun u => if h : u ∈ F then Classical.choose h else 0
  have hg : ∀ u ∈ F, g u ∈ X.L ∧ uc (IR I) (g u) = u := by
    intro u hu
    have := Classical.choose_spec hu
    simp only [g, dif_pos hu]
    exact ⟨this.1, this.2.2⟩
  refine ⟨∑ u ∈ hfin.toFinset, ‖p2 (IR I) (g u)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    fun y hy hyC => ?_⟩
  have hu : uc (IR I) y ∈ F := ⟨y, hy, hyC, rfl⟩
  refine ⟨g (uc (IR I) y), (hg _ hu).1, (hg _ hu).2, ?_⟩
  exact Finset.single_le_sum (f := fun u => ‖p2 (IR I) (g u)‖) (fun _ _ => norm_nonneg _)
    (hfin.mem_toFinset.2 hu)

end Lat

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
end

namespace ReciprocityTheory.ChartRestriction.G.I2

open Complex NumberField
open scoped InnerProductSpace

noncomputable section

namespace Col

theorem extend_hom {M : Type} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (N : Submodule ℤ M) (hsat : ∀ (k : ℤ) (x : M), k ≠ 0 → k • x ∈ N → x ∈ N) (ψ : N →ₗ[ℤ] ℤ) :
    ∃ Ψ : M →ₗ[ℤ] ℤ, ∀ x : N, Ψ x = ψ x := by
  have : Module.IsTorsionFree ℤ (M ⧸ N) := by
    refine ⟨fun k hk a b hab => ?_⟩
    induction a using Submodule.Quotient.induction_on with | H x => ?_
    induction b using Submodule.Quotient.induction_on with | H y => ?_
    simp only at hab
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hab
    rw [Submodule.Quotient.eq]
    exact hsat k (x - y) hk.ne_zero (by simpa only [smul_sub] using hab)
  have : Module.Free ℤ (M ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id) (Submodule.mkQ_surjective N)
  have hmem : ∀ x : M, x - σ (N.mkQ x) ∈ N := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub]
    have := LinearMap.congr_fun hσ (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let p : M →ₗ[ℤ] N := LinearMap.codRestrict N (LinearMap.id - σ ∘ₗ N.mkQ) (fun x => hmem x)
  refine ⟨ψ ∘ₗ p, fun x => ?_⟩
  have : p x = x := by
    apply Subtype.ext
    simp [p, (Submodule.Quotient.mk_eq_zero N).2 x.2]
  simp [this]

variable {E : Type} [Field E] [NumberField E]

def GB (X : PT E) (I : Submodule ℤ (Vsp X.dim)) : Submodule ℤ (EuclideanSpace ℂ (Fin (gB (IR I)))) :=
  (Ip X I).map (((wmap (IR I)).toLinearMap).restrictScalars ℤ)

theorem mem_GB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {t : EuclideanSpace ℂ (Fin (gB (IR I)))} :
    t ∈ GB X I ↔ ∃ x ∈ Ip X I, wmap (IR I) x = t := by
  unfold GB
  rw [Submodule.mem_map]
  rfl

theorem wmap_mem_GB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {x : Vsp X.dim} (hx : x ∈ Ip X I) :
    wmap (IR I) x ∈ GB X I := mem_GB.2 ⟨x, hx, rfl⟩

section GBsec

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem GB_norm {t : EuclideanSpace ℂ (Fin (gB (IR I)))} (ht : t ∈ GB X I) (h0 : t ≠ 0) :
    P.th ≤ ‖t‖ := by
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 ht
  rw [norm_wmap (hK_of hI)]
  by_cases hxI : x ∈ I
  · exfalso; apply h0
    rw [← norm_eq_zero, norm_wmap (hK_of hI), proj_two_of_mem (hK_of hI) (mem_IR hxI), norm_zero]
  · exact gap_le_norm_proj_two hI hx hxI

theorem GB_discrete : DiscreteTopology (GB X I) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have : ({0} : Set (GB X I)) = Subtype.val ⁻¹' Metric.ball 0 P.th := by
    ext ⟨t, ht⟩
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · intro h
      have : t = 0 := congrArg Subtype.val h
      rw [this, norm_zero]; exact th_pos P
    · intro h
      by_contra hne
      have h0 : t ≠ 0 := fun h' => hne (Subtype.ext h')
      exact absurd (GB_norm hI ht h0) (not_le.2 h)
  rw [this]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

theorem GB_span (hP : Ext.PackingCount) :
    Submodule.span ℝ (GB X I : Set (EuclideanSpace ℂ (Fin (gB (IR I))))) = ⊤ := by
  have hK := hK_of hI
  set C0 := ∑ i, ‖X.b i‖ with hC0
  have hC0n : 0 ≤ C0 := Finset.sum_nonneg fun _ _ => norm_nonneg _
  obtain ⟨M, hM0, hM⟩ := reps_bdd hI hP C0
  have approx : ∀ t, ∃ s ∈ GB X I, ‖t - s‖ ≤ C0 + M := by
    intro t
    set v := jj (IR I) t
    set γ : Vsp X.dim := (ZSpan.floor X.b v : Vsp X.dim)
    have hγ : γ ∈ X.L := (ZSpan.floor X.b v).2
    have hvγ : ‖v - γ‖ ≤ C0 := by
      rw [← ZSpan.fract_apply]; exact ZSpan.norm_fract_le _ _
    have hucv : uc (IR I) v = 0 := by simp [uc, v, z_jj]
    have huc : ‖uc (IR I) γ‖ ≤ C0 := by
      have : uc (IR I) γ = -uc (IR I) (v - γ) := by rw [uc_sub, hucv]; simp
      rw [this, norm_neg]
      exact (norm_uc_le hI.iso _).trans hvγ
    obtain ⟨y', hy'L, hy'u, hy'M⟩ := hM γ hγ huc
    have hIp : γ - y' ∈ Ip X I := by
      refine ⟨X.L.sub_mem hγ hy'L, fun a ha => ?_⟩
      rw [← (isU_uc (I := I) (γ - y')).2 a (mem_IR ha), uc_sub, hy'u, sub_self, inner_zero_left]
    refine ⟨wmap (IR I) (γ - y'), wmap_mem_GB hIp, ?_⟩
    have ht : t = wmap (IR I) v := (wmap_jj _ t).symm
    have : t - wmap (IR I) (γ - y') = wmap (IR I) (v - γ) + wmap (IR I) y' := by
      rw [ht, ← map_sub, ← map_add (f := _)]; congr 1; abel
    rw [this]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_wmap hK]; exact (norm_proj_two_le hK _).trans hvγ
    · rw [norm_wmap hK]; exact hy'M
  by_contra hW
  rw [← Submodule.orthogonal_eq_bot_iff] at hW
  obtain ⟨t0, ht0, ht0ne⟩ := (Submodule.ne_bot_iff _).1 hW
  have hn0 : 0 < ‖t0‖ := norm_pos_iff.2 ht0ne
  set c : ℝ := (C0 + M + 1) / ‖t0‖
  set t := c • t0
  have htW : t ∈ (Submodule.span ℝ (GB X I : Set (EuclideanSpace ℂ (Fin (gB (IR I))))))ᗮ :=
    Submodule.smul_mem _ _ ht0
  have hnt : ‖t‖ = C0 + M + 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [c]; field_simp
  obtain ⟨s, hs, hts⟩ := approx t
  have hin : ⟪s, t⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span hs) htW
  have h2 := norm_sub_sq_real t s
  rw [real_inner_comm, hin] at h2
  have : ‖t‖ ^ 2 ≤ ‖t - s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
  have h3 : ‖t - s‖ < ‖t‖ := by rw [hnt]; linarith
  nlinarith [norm_nonneg (t - s), norm_nonneg t]

end GBsec

section GBsec2

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem GB_perfect (φ : GB X I →+ ℤ) :
    ∃ x0 ∈ Ip X I, ∀ x (hx : x ∈ Ip X I),
      (φ ⟨wmap (IR I) x, wmap_mem_GB hx⟩ : ℝ) = (Hf (wmap (IR I) x0) (wmap (IR I) x)).im := by
  have hK := hK_of hI
  set N : Submodule ℤ X.L := (Ip X I).comap X.L.subtype with hN
  have hsat : ∀ (k : ℤ) (x : X.L), k ≠ 0 → k • x ∈ N → x ∈ N := by
    intro k x hk hx
    refine ⟨x.2, fun a ha => ?_⟩
    have h := hx.2 a ha
    simp only [Submodule.coe_subtype, Submodule.coe_smul] at h
    rw [← Int.cast_smul_eq_zsmul ℂ, Hf_smul_l, Complex.mul_im] at h
    simp only [Complex.intCast_re, Complex.intCast_im, zero_mul, add_zero, mul_eq_zero,
      Int.cast_eq_zero] at h
    rcases h with h | h
    · exact absurd h hk
    · exact h
  let ψ0 : N →+ GB X I :=
    { toFun := fun x => ⟨wmap (IR I) ((x : X.L) : Vsp X.dim), wmap_mem_GB x.2⟩
      map_zero' := by ext1; simp
      map_add' := by intro x y; ext1; simp }
  obtain ⟨Ψ, hΨ⟩ := extend_hom N hsat (φ.comp ψ0).toIntLinearMap
  obtain ⟨x0, hx0L, hx0⟩ := X.perfect Ψ.toAddMonoidHom
  have hx0I : x0 ∈ Ip X I := by
    refine ⟨hx0L, fun a ha => ?_⟩
    have haIp : a ∈ Ip X I := ⟨hI.le ha, fun b hb => hI.iso a ha b hb⟩
    have h1 := hx0 ⟨a, hI.le ha⟩
    have h2 := hΨ ⟨⟨a, hI.le ha⟩, haIp⟩
    have hw : wmap (IR I) a = 0 := by
      rw [← norm_eq_zero, norm_wmap hK, proj_two_of_mem hK (mem_IR ha), norm_zero]
    have h3 : ψ0 ⟨⟨a, hI.le ha⟩, haIp⟩ = 0 := Subtype.ext hw
    simp only [LinearMap.toAddMonoidHom_coe] at h1
    rw [h2] at h1
    simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.coe_comp, Function.comp_apply, h3,
      map_zero, Int.cast_zero] at h1
    exact h1.symm
  refine ⟨x0, hx0I, fun x hx => ?_⟩
  have h1 := hx0 ⟨x, hx.1⟩
  have h2 := hΨ ⟨⟨x, hx.1⟩, hx⟩
  simp only [LinearMap.toAddMonoidHom_coe] at h1
  rw [h2] at h1
  rw [Hf_wmap hK, herm_im_proj_two hI hx0I hx]
  exact h1

end GBsec2

def bB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
    (hP : Ext.PackingCount) :
    Module.Basis (Fin (2 * Fintype.card (Fin (gB (IR I))))) ℝ (EuclideanSpace ℂ (Fin (gB (IR I)))) :=
  haveI := GB_discrete hI
  haveI : IsZLattice ℝ (GB X I) := ⟨GB_span hI hP⟩
  haveI := ZLattice.module_free ℝ (GB X I)
  (Module.Basis.ofZLatticeBasis ℝ (GB X I) (Module.Free.chooseBasis ℤ (GB X I))).reindex
    (Fintype.equivFinOfCardEq (by
      rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ, finrank_real_of_complex,
        finrank_euclideanSpace]))

theorem lat_bB {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
    (hP : Ext.PackingCount) : lat (bB hI hP) = GB X I := by
  haveI := GB_discrete hI
  haveI : IsZLattice ℝ (GB X I) := ⟨GB_span hI hP⟩
  haveI := ZLattice.module_free ℝ (GB X I)
  rw [lat, bB, Module.Basis.range_reindex, Module.Basis.ofZLatticeBasis_span]

theorem exp_sign (q : ℕ) (k : ℤ) :
    cexp (-(Real.pi * q * (k : ℝ)) * I) = (((-1 : ℝ) ^ k : ℝ) : ℂ) ^ q := by
  have e1 : (-(Real.pi * q * (k : ℝ)) * I : ℂ) = ((-(Real.pi * q * k) : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : Real.pi * q * k = ((q * k : ℤ) : ℝ) * Real.pi := by push_cast; ring
  rw [e1, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, e2,
    Real.cos_int_mul_pi, Real.sin_int_mul_pi, neg_zero, Complex.ofReal_zero, zero_mul, add_zero,
    ← Complex.ofReal_pow]
  congr 1
  rw [← zpow_natCast, ← zpow_mul, mul_comm]

open scoped Classical in
open Classical in
def kaB (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (q : ℕ) (t : EuclideanSpace ℂ (Fin (gB (IR I)))) : ℂ :=
  if h : ∃ x ∈ Ip X I, wmap (IR I) x = t then (X.eps h.choose : ℂ) ^ q else 1

section GT

variable {X : PT E} {I : Submodule ℤ (Vsp X.dim)} {DF : ℕ} {P : Par X DF} (hI : IsSplit P I)
include hI

theorem kaB_wmap (q : ℕ) {x : Vsp X.dim} (hx : x ∈ Ip X I) : kaB X I q (wmap (IR I) x) = (X.eps x : ℂ) ^ q := by
  have h : ∃ x' ∈ Ip X I, wmap (IR I) x' = wmap (IR I) x := ⟨x, hx, rfl⟩
  rw [kaB, dite_eq_left h]
  have hs := h.choose_spec
  have hp : p2 (IR I) h.choose = p2 (IR I) x := by
    rw [← jj_wmap' (hK_of hI), ← jj_wmap' (hK_of hI) x, hs.2]
  rw [sign_eq_of_proj_two_eq hI hs.1 hx hp]

variable (hP : Ext.PackingCount)

def YB (q : ℕ) : GT (Fin (gB (IR I))) where
  b := bB hI hP
  integral := by
    intro x y hx hy
    rw [lat_bB] at hx hy
    obtain ⟨x', hx', rfl⟩ := mem_GB.1 hx
    obtain ⟨y', hy', rfl⟩ := mem_GB.1 hy
    rw [Hf_wmap (hK_of hI), herm_im_proj_two hI hx' hy']
    exact X.integral x' y' hx'.1 hy'.1
  perfect := by
    intro φ
    have hl := lat_bB hI hP
    let ι0 : GB X I →+ lat (bB hI hP) :=
      { toFun := fun t => ⟨t.1, by rw [hl]; exact t.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
    obtain ⟨x0, hx0, h0⟩ := GB_perfect hI (φ.comp ι0)
    refine ⟨wmap (IR I) x0, by rw [hl]; exact wmap_mem_GB hx0, fun y => ?_⟩
    have hyG : (y : EuclideanSpace ℂ (Fin (gB (IR I)))) ∈ GB X I := (le_of_eq hl) y.2
    obtain ⟨x, hx, hxy⟩ := mem_GB.1 hyG
    have := h0 x hx
    have hy : ι0 ⟨wmap (IR I) x, wmap_mem_GB hx⟩ = y := Subtype.ext hxy
    rw [AddMonoidHom.comp_apply, hy] at this
    rw [this, hxy]
  ka := kaB X I q
  ka_abs := by
    intro t ht
    rw [lat_bB] at ht
    obtain ⟨x, hx, rfl⟩ := mem_GB.1 ht
    rw [kaB_wmap hI _ hx, norm_pow]
    rcases X.eps_pm x hx.1 with h | h <;> simp [h]

theorem YB_lat (q : ℕ) {t : EuclideanSpace ℂ (Fin (gB (IR I)))} : t ∈ lat (YB hI hP q).b ↔ t ∈ GB X I := by
  show t ∈ lat (bB hI hP) ↔ t ∈ GB X I
  rw [lat_bB]

theorem YB_ka (q : ℕ) {x : Vsp X.dim} (hx : x ∈ Ip X I) : (YB hI hP q).ka (wmap (IR I) x) = (X.eps x : ℂ) ^ q := kaB_wmap hI q hx

theorem YB_coc (q : ℕ) : (YB hI hP q).Coc q := by
  intro γ hγ γ' hγ'
  rw [YB_lat] at hγ hγ'
  obtain ⟨x, hx, rfl⟩ := mem_GB.1 hγ
  obtain ⟨y, hy, rfl⟩ := mem_GB.1 hγ'
  have hxy : x + y ∈ Ip X I := (Ip X I).add_mem hx hy
  obtain ⟨k, hk⟩ := X.integral x y hx.1 hy.1
  rw [← map_add (f := _), YB_ka hI hP q hxy, YB_ka hI hP q hx, YB_ka hI hP q hy, Hf_wmap (hK_of hI),
    herm_im_proj_two hI hx hy, hk, exp_sign]
  have he := X.eps_add x hx.1 y hy.1
  rw [hk, show Real.pi * (k : ℝ) = (k : ℝ) * Real.pi by ring, Real.cos_int_mul_pi] at he
  have hc : (X.eps (x + y) : ℂ) = (X.eps x : ℂ) * X.eps y * (((-1 : ℝ) ^ k : ℝ) : ℂ) := by
    have := congrArg (fun r : ℝ => (r : ℂ)) he
    push_cast at this ⊢
    exact this
  rw [hc, mul_pow, mul_pow]

end GT

end Col

end

end ReciprocityTheory.ChartRestriction.G.I2
