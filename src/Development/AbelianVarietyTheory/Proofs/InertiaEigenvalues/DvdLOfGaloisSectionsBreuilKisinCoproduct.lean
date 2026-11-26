module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinPrismCoproduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimeProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinLiftCompatibleBdRPrisms

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSections
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSection
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltOfCompatibleRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem tilt_of_compatible_roots : ∀ (l : ℕ) [Fact l.Prime] (s : ℕ → OC l),
    (∀ n, s (n + 1) ^ l = s n) → ∃ y : OCb l, ∀ n, GlobalTheory.MemLoc.rootT y n = s n := by
  intro l _ s hs
  exact (GlobalTheory.MemLoc.tilt_facts l).1 s hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongr
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mem_OC_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : ℂ_[l]) (c : OC l)
    (h : a ^ N = (c : ℂ_[l])) : a ∈ 𝓞_ℂ_[l] := by
  rw [GlobalTheory.RingBasics.mem_OC]
  have h1 := (GlobalTheory.RingBasics.mem_OC _).1 c.2
  rw [← h, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1

theorem exists_OC_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {D : Type} [CommRing D] [IsDomain D] (f : OC l →+* D)
    {N : ℕ} (hN : 0 < N) (c : OC l) (r : D) (h : r ^ N = f c) : ∃ s : OC l, f s = r := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (c : ℂ_[l]) hN
  haveI : NeZero (N : ℂ_[l]) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[l] N
  let a' : OC l := ⟨a, mem_OC_of_pow_eq hN a c ha⟩
  let ζ' : OC l := ⟨ζ, mem_OC_of_pow_eq hN ζ 1 hζ.pow_eq_one⟩
  have hζ' : IsPrimitiveRoot ζ' N :=
    IsPrimitiveRoot.of_map_of_injective (f := (𝓞_ℂ_[l]).subtype) hζ Subtype.val_injective
  have ha' : a' ^ N = c := Subtype.ext ha
  have hp := congrArg (Polynomial.eval₂ f r) (X_pow_sub_C_eq_prod hζ' hN ha')
  rw [Polynomial.eval₂_finsetProd, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, h,
    sub_self, eq_comm, Finset.prod_eq_zero_iff] at hp
  obtain ⟨i, -, hi⟩ := hp
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hi
  exact ⟨_, hi.symm⟩

theorem exists_alg_eq_of_pow_eq {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : 0 < N) (a : Om l) (s : ℂ_[l])
    (h : s ^ N = (a : ℂ_[l])) : ∃ z : Om l, s = (z : ℂ_[l]) := by
  have hf : (Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)) ≠ 0 :=
    Polynomial.X_pow_sub_C_ne_zero hN a
  have hroot : ((Polynomial.X ^ N - Polynomial.C a : Polynomial (Om l)).map
      (algebraMap (Om l) ℂ_[l])).IsRoot s := by
    simp only [Polynomial.IsRoot, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
    rw [h]
    exact sub_self _
  obtain ⟨z, hz⟩ := (IsAlgClosed.splits _).mem_range_of_isRoot hf hroot
  exact ⟨z, hz.symm⟩

theorem eq_of_forall_dvd_root_sub {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [CharP O l] [PerfectRing O l]
    (c : O) [IsHausdorff (Ideal.span {c}) O] (v w : O)
    (h : ∀ n : ℕ, c ∣ ((frobeniusEquiv O l).symm)^[n] v - ((frobeniusEquiv O l).symm)^[n] w) : v = w := by
  have hp : ∀ (n : ℕ) (x : O), (((frobeniusEquiv O l).symm)^[n] x) ^ (l ^ n) = x := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih => intro x; rw [Function.iterate_succ_apply, pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := Ideal.span {c}) _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have h1 := pow_dvd_pow_of_dvd (h n) (l ^ n)
  rw [sub_pow_char_pow, hp, hp] at h1
  exact (pow_dvd_pow c (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le).trans h1

theorem exists_gal_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  intro l _ K bk O _ _ _ _ _ ψ h0 hu hc v hv
  have hl : 0 < l := (Fact.out : l.Prime).pos
  obtain ⟨f, hf, hinj, hdom, hmod⟩ := GlobalTheory.T.exists_injective_map_integers_Cl_to_wittQuotient l K bk O ψ h0 hu hc
  obtain ⟨hprime, hπ⟩ := GlobalTheory.T.breuilKisin_prime_uniformizer_class l K bk
  obtain ⟨halg, hfix⟩ := GlobalTheory.T.untiltOfTiltRoot_flat_algebraic_and_galois_fix l K bk
  set π : ↥(OL K) := bk.str.symm (Ideal.Quotient.mk _ (X : bk.S)) with hπd
  have hft : ∀ y : OCb l, f y.untilt = Ideal.Quotient.mk _ (WittVector.teichmuller l (ψ y)) := fun y => by
    rw [← WittVector.fontaineTheta_teichmuller, ← WittVector.map_teichmuller]
    exact hf _
  let r : ℕ → WittVector l O ⧸ Ideal.span {WittVector.map ψ (bk.ev bk.E)} := fun n =>
    Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v))
  have hr0 : r 0 = f bk.flat.untilt := by
    rw [hft]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 hv)
  have hrs : ∀ n, r (n + 1) ^ l = r n := fun n => by
    simp only [r]
    rw [← map_pow, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  have hrn : ∀ n, r n ^ (l ^ n) = f bk.flat.untilt := fun n => by
    induction n with
    | zero => rw [pow_zero, pow_one, hr0]
    | succ n ih => rw [pow_succ', pow_mul, hrs, ih]
  choose s hs using fun n => exists_OC_eq_of_pow_eq f (pow_pos hl n) _ _ (hrn n)
  have hss : ∀ n, s (n + 1) ^ l = s n := fun n => hinj (by rw [map_pow, hs, hs, hrs])
  have hsn : ∀ n, s n ^ (l ^ n) = bk.flat.untilt := fun n => hinj (by rw [map_pow, hs, hrn])
  have hπc : ((bk.flat.untilt : OC l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l]) := by
    rw [← hπ, coe_intToOC]
  have hcoe : Function.Injective (fun z : Om l => (z : ℂ_[l])) := (algebraMap (Om l) ℂ_[l]).injective
  have hcp : ∀ (z : Om l) (m : ℕ), ((z ^ m : Om l) : ℂ_[l]) = (z : ℂ_[l]) ^ m :=
    fun z m => map_pow (algebraMap (Om l) ℂ_[l]) z m
  choose z hz using fun n => exists_alg_eq_of_pow_eq (pow_pos hl n) ((π : ↥K.1) : Om l) (s n : ℂ_[l])
    (by rw [← hπc, ← hsn n, SubmonoidClass.coe_pow])
  choose y hy using halg
  have hts : ∀ n, GlobalTheory.MemLoc.rootT bk.flat (n + 1) ^ l = GlobalTheory.MemLoc.rootT bk.flat n := fun n => by
    rw [GlobalTheory.MemLoc.rootT, GlobalTheory.MemLoc.rootT, ← map_pow, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  obtain ⟨g, hg⟩ := GlobalTheory.T.galois_transitive_on_prime_power_root_systems l K π hprime y z
    (hcoe (by
      change ((y 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hy, ← hπc]
      rfl))
    (hcoe (by
      change ((z 0 : Om l) : ℂ_[l]) = (((π : ↥K.1) : Om l) : ℂ_[l])
      rw [← hz, ← hπc, ← hsn 0, pow_zero, pow_one]))
    (fun n => hcoe (by
      change ((y (n + 1) ^ l : Om l) : ℂ_[l]) = ((y n : Om l) : ℂ_[l])
      rw [hcp, ← hy, ← hy, ← hts n, SubmonoidClass.coe_pow]))
    (fun n => hcoe (by
      change ((z (n + 1) ^ l : Om l) : ℂ_[l]) = ((z n : Om l) : ℂ_[l])
      rw [hcp, ← hz, ← hz, ← hss n, SubmonoidClass.coe_pow]))
  obtain ⟨w, hw⟩ := GlobalTheory.tilt_of_compatible_roots l s hss
  have hgw : Per.σF (g : GQ l) bk.flat = w := hfix _ _ fun n => Subtype.ext (by
    refine (GlobalTheory.RingIface.sigO_coe l (g : GQ l) (GlobalTheory.MemLoc.rootT bk.flat n)).trans ?_
    rw [hy, hw, hz, ← hg n]
    exact GlobalTheory.RingBasics.σC_coe _ _)
  refine ⟨g, ?_⟩
  rw [hgw]
  refine eq_of_forall_dvd_root_sub (l := l) (ψ bk.flat) v (ψ w) fun n => ?_
  have hψ : ∀ m, ψ (((frobeniusEquiv (OCb l) l).symm)^[m] w) = ((frobeniusEquiv O l).symm)^[m] (ψ w) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, RingHom.map_frobeniusEquiv_symm]
  have h1 := hft (((frobeniusEquiv (OCb l) l).symm)^[n] w)
  have h2 : f (s n) = Ideal.Quotient.mk _ (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w))) := by
    rw [← hw n, ← hψ]
    exact h1
  have h3 := hmod (WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] v) -
      WittVector.teichmuller l (((frobeniusEquiv O l).symm)^[n] (ψ w)))
    (by rw [map_sub, ← h2, hs, sub_self]; exact dvd_zero _)
  rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero] at h3
  exact (dvd_pow_self _ bk.deg_pos.ne').trans h3

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjOfTeichmullerCongrStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_conj_of_teichmuller_congr : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O), ψ bk.flat ≠ 0 → ¬ IsUnit (ψ bk.flat) → IsAdicComplete (Ideal.span {ψ bk.flat}) O → ∀ v : O, WittVector.map ψ (bk.ev bk.E) ∣ WittVector.teichmuller l v - WittVector.teichmuller l (ψ bk.flat) → ∃ g : ↥(GK K), v = ψ (Per.σF (g : GQ l) bk.flat) := by
  first | exact @GlobalTheory.BSP.exists_gal_of_teichmuller_congr | exact GlobalTheory.BSP.exists_gal_of_teichmuller_congr | (intros; apply GlobalTheory.BSP.exists_gal_of_teichmuller_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgree
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem envExt_sub_mem {S A C : Type} [CommRing S] [CommRing A] [CommRing C] (G G' : A →+* C) (s : S →+* A)
    (J : Ideal S) (x a : A) (hs : G.comp s = G'.comp s) (ha : G a = G' a) (hx : x - a ∈ J.map s) :
    G x - G' x ∈ J.map (G.comp s) := by
  have e : G x - G' x = G (x - a) - G' (x - a) := by rw [map_sub, map_sub, ha]; ring
  rw [e]
  refine Ideal.sub_mem _ ?_ ?_
  · rw [← Ideal.map_map]; exact Ideal.mem_map_of_mem G hx
  · rw [hs, ← Ideal.map_map]; exact Ideal.mem_map_of_mem G' hx

theorem envExt_haus {C : Type} [CommRing C] (I : Ideal C) (h : IsHausdorff I C) (z : C) (hz : ∀ n : ℕ, z ∈ I ^ n) :
    z = 0 :=
  h.haus z fun n => by
    rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top]
    exact hz n


set_option maxHeartbeats 1600000 in
theorem envExt_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  intro l _ K bk B d p En C _ φ F F' hl hF hF' hb hX hd hH

  have hw : F En.w = F' En.w := by
    have h1 := congrArg F En.w_eq
    have h2 := congrArg F' En.w_eq
    rw [map_add (f := _), map_mul] at h1 h2
    have h3 : F (En.inl.f d) * F En.w = F (En.inl.f d) * F' En.w := by
      rw [hb d] at h1 ⊢
      rw [hb p] at h1
      rw [hX] at h1
      rw [h2] at h1
      linear_combination -h1
    exact (mul_cancel_left_mem_nonZeroDivisors hd).1 h3

  have hδ : ∀ a, F a = F' a → F (En.Q.D.δ a) = F' (En.Q.D.δ a) := by
    intro a ha
    have e1 := hF a
    have e2 := hF' a
    rw [En.Q.D.φ_eq, map_add (f := _), map_mul, map_pow, map_natCast] at e1 e2
    rw [← ha] at e2
    have : ((l : ℕ) : C) * (F (En.Q.D.δ a) - F' (En.Q.D.δ a)) = 0 := by
      linear_combination e1 - e2
    exact sub_eq_zero.1 (hl _ this)
  have hit : ∀ i : ℕ, F (En.Q.D.δ^[i] En.w) = F' (En.Q.D.δ^[i] En.w) := by
    intro i
    induction i with
    | zero => exact hw
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact hδ _ ih
  have hbasis : ∀ α, F (En.tb.b α) = F' (En.tb.b α) := by
    intro α
    rw [En.tb_b, map_finsuppProd, map_finsuppProd]
    refine Finsupp.prod_congr fun i _ => ?_
    rw [map_pow, map_pow, hit i]
  have hcomp : F.comp En.inl.f = F'.comp En.inl.f := RingHom.ext hb
  have key : ∀ x (n : ℕ), F x - F' x ∈ ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I) ^ n).map (F.comp En.inl.f) := by
    intro x n
    have hfin := En.tb.fin x n
    have happ := En.tb.approx x n hfin.toFinset (fun i hi => by
      by_contra h
      exact hi (hfin.mem_toFinset.2 h))
    have hsum : F (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) =
        F' (∑ i ∈ hfin.toFinset, En.inl.f (En.tb.c i x) * En.tb.b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, hb, hbasis]
    exact envExt_sub_mem F F' En.inl.f _ _ _ hcomp hsum happ
  ext x
  exact sub_eq_zero.1 (envExt_haus _ hH _ fun n => by rw [← Ideal.map_pow]; exact key x n)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductHomEqOfAgreeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (d p : B.A) (En : Env bk B d p) (C : Type) [CommRing C] (φ : C →+* C) (F F' : En.Q.A →+* C), (∀ c : C, ((l : ℕ) : C) * c = 0 → c = 0) → (∀ a, F (En.Q.D.φ a) = φ (F a)) → (∀ a, F' (En.Q.D.φ a) = φ (F' a)) → (∀ b, F (En.inl.f b) = F' (En.inl.f b)) → F (BK.hf En.inr X) = F' (BK.hf En.inr X) → F (En.inl.f d) ∈ nonZeroDivisors C → IsHausdorff ((Ideal.span {((l : ℕ) : B.A)} ⊔ B.I).map (F.comp En.inl.f)) C → F = F' := by
  first | exact @GlobalTheory.BSP.envExt_agree | exact GlobalTheory.BSP.envExt_agree | (intros; apply GlobalTheory.BSP.envExt_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLift
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterate
open scoped NNReal
open Finset

namespace GlobalTheory.DworkGhost


open scoped Classical in
open Classical in
noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by exact i.isLt

theorem coeff_spec {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dite_eq_left h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring

theorem ghost_eq {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))

theorem exists_witt_ghost_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]

end GlobalTheory.DworkGhost
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterateStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion
open scoped NNReal

namespace GlobalTheory

theorem WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsionStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLift
open scoped NNReal

namespace GlobalTheory.DworkLift

theorem exists_frobenius_compatible_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
    ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O,
      (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  intro l _ A _ φ hφ htor O _ _ f
  have hex := GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate l A φ hφ
  have inj := GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion l A htor
  let s : A → WittVector l A := fun a => Classical.choose (hex a)
  have hs : ∀ a n, WittVector.ghostComponent n (s a) = φ^[n] a := fun a => Classical.choose_spec (hex a)
  have hit : ∀ (n : ℕ) (a : A), φ^[n] a = (φ ^ n) a := fun n a => by rw [RingHom.coe_pow]
  let S : A →+* WittVector l A :=
    { toFun := s
      map_one' := inj _ _ fun n => by rw [hs, map_one, hit, map_one]
      map_mul' := fun a b => inj _ _ fun n => by rw [map_mul, hs, hs, hs, hit, hit, hit, map_mul]
      map_zero' := inj _ _ fun n => by rw [hs, map_zero, hit, map_zero]
      map_add' := fun a b => inj _ _ fun n => by rw [map_add (f := _), hs, hs, hs, hit, hit, hit, map_add (f := _)] }
  have hS0 : ∀ a, (S a).coeff 0 = a := fun a => by
    change (s a).coeff 0 = a
    have h := hs a 0
    rw [WittVector.ghostComponent_apply, wittPolynomial_zero] at h
    simpa using h
  have hSφ : ∀ a, S (φ a) = WittVector.frobenius (S a) := fun a => inj _ _ fun n => by
    change WittVector.ghostComponent n (s (φ a)) = WittVector.ghostComponent n (WittVector.frobenius (s a))
    rw [WittVector.ghostComponent_frobenius, hs, hs, Function.iterate_succ_apply]
  refine ⟨(WittVector.map f).comp S, fun a => ?_, fun a => ?_⟩
  · simp only [RingHom.comp_apply, WittVector.map_coeff, hS0]
  · simp only [RingHom.comp_apply, hSφ]
    exact WittVector.IsPoly.map (WittVector.frobenius_isPoly l) f (S a)

end GlobalTheory.DworkLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLiftStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_compatible_wittVector_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelf
open scoped NNReal

namespace GlobalTheory


open _root_.WittVector in
theorem wittVector_iterate_frobenius_of_eq_pow {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    (y : WittVector l O) (h : (WittVector.frobenius (p := l) (R := O)) y = y ^ l) (k : ℕ) :
    (WittVector.frobenius (p := l) (R := O))^[k] y = y ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, map_pow, h, ← pow_mul, pow_succ', mul_comm]


open _root_.WittVector in
theorem wittVector_coeff_iterate_frobenius {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O]
    [CharP O l] (y : WittVector l O) (k n : ℕ) :
    ((WittVector.frobenius (p := l) (R := O))^[k] y).coeff n = y.coeff n ^ l ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', WittVector.coeff_frobenius_charP, ih, ← pow_mul, ← pow_succ]


open _root_.WittVector in
theorem wittVector_eq_teichmuller_of_frobenius_eq_pow :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l]
      (y : WittVector l O), WittVector.frobenius y = y ^ l →
      y = WittVector.teichmuller l (y.coeff 0) := by
  intro l _ O _ _ _ y h

  have hdiv : (l : WittVector l O) ∣ y - WittVector.teichmuller l (y.coeff 0) := by
    have h0 : ∀ i < 1, (y - WittVector.teichmuller l (y.coeff 0)).coeff i = 0 := by
      intro i hi
      obtain rfl : i = 0 := by omega
      have hc := map_sub (WittVector.constantCoeff (p := l) (R := O)) y
        (WittVector.teichmuller l (y.coeff 0))
      simp only [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self] at hc
      exact hc
    obtain ⟨w, hw⟩ := (WittVector.frobenius_bijective l O).2
      ((y - WittVector.teichmuller l (y.coeff 0)).shift 1)
    refine ⟨w, ?_⟩
    rw [WittVector.eq_iterate_verschiebung h0, Function.iterate_one, ← hw,
      WittVector.verschiebung_frobenius, mul_comm]
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [WittVector.teichmuller_coeff_pos l _ n hn]

  obtain ⟨c, hc⟩ := dvd_sub_pow_of_dvd_sub hdiv n
  have hy : y ^ l ^ n = WittVector.teichmuller l (y.coeff 0 ^ l ^ n) +
      c * (l : WittVector l O) ^ (n + 1) := by
    rw [map_pow, mul_comm c]
    exact sub_eq_iff_eq_add'.mp hc
  have hcoeff : (y ^ l ^ n).coeff n = 0 := by
    rw [hy, WittVector.coeff_add_of_disjoint]
    · rw [WittVector.teichmuller_coeff_pos l _ n hn,
        WittVector.mul_pow_charP_coeff_zero _ (by omega : n < n + 1), add_zero]
    · intro m
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · exact Or.inr (WittVector.mul_pow_charP_coeff_zero _ (by omega))
      · exact Or.inl (WittVector.teichmuller_coeff_pos l _ m hm)

  rw [← wittVector_iterate_frobenius_of_eq_pow y h n, wittVector_coeff_iterate_frobenius] at hcoeff
  apply (bijective_iterateFrobenius O l n).1
  show y.coeff n ^ l ^ n = (0 : O) ^ l ^ n
  rw [hcoeff, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorEqTeichmullerOfFrobeniusEqPowSelfStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [CharP O l] [PerfectRing O l] (y : WittVector l O), WittVector.frobenius y = y ^ l → y = WittVector.teichmuller l (y.coeff 0) := by
  first | exact @GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | exact GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow | (intros; apply GlobalTheory.wittVector_eq_teichmuller_of_frobenius_eq_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZero
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZero
open scoped NNReal

namespace GlobalTheory.WittMapUniq

open _root_.WittVector

theorem exists_pow_pow_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]

theorem eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)

end GlobalTheory.WittMapUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorRingHomEqMapOfCoeffZeroStatement
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l] (F : WittVector l R →+* WittVector l O) (ψ : R →+* O), (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  first | exact @GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | exact GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | (intros; apply GlobalTheory.WittMapUniq.eq_map_of_coeff_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isHausdorff_of_le_ideal {R : Type} [CommRing R] {I J : Ideal R} (h : I ≤ J) (hJ : IsHausdorff J R) :
    IsHausdorff I R := by
  refine ⟨fun x hx => hJ.haus x fun n => ?_⟩
  have h1 := hx n
  rw [SModEq.sub_mem] at h1 ⊢
  exact Submodule.smul_mono_left (Ideal.pow_right_mono h n) h1

theorem map_frobenius_charP {l : ℕ} [Fact l.Prime] {R O : Type} [CommRing R] [CharP R l] [CommRing O] [CharP O l]
    (ψ : R →+* O) (x : WittVector l R) :
    WittVector.map ψ (WittVector.frobenius x) = WittVector.frobenius (WittVector.map ψ x) := by
  ext n
  rw [WittVector.map_coeff, WittVector.coeff_frobenius_charP, WittVector.coeff_frobenius_charP,
    WittVector.map_coeff, map_pow]

theorem hom_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (a : P.A) : (g.comp f).f a = g.f (f.f a) := rfl

theorem hom_eq_id_apply {l : ℕ} {R : Type} [CommRing R] {P P' : Obj l R} (g : Hom P' P) (f : Hom P P')
    (h : g.comp f = Hom.id P) (a : P.A) : g.f (f.f a) = a := by
  rw [← hom_comp_apply, h]; rfl

theorem hom_eq_comp_apply {l : ℕ} {R : Type} [CommRing R] {P P' P'' Q : Obj l R} (g : Hom P' P'') (f : Hom P P')
    (g' : Hom Q P'') (f' : Hom P Q) (h : g.comp f = g'.comp f') (a : P.A) : g.f (f.f a) = g'.f (f'.f a) := by
  rw [← hom_comp_apply, h]; rfl

theorem mapE_facts {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (O : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O) (hx0 : ψ bk.flat ≠ 0)
    (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O) :
    WittVector.map ψ (bk.ev bk.E) ∈ nonZeroDivisors (WittVector l O) ∧
    IsHausdorff ((Ideal.span {((l : ℕ) : WittVector l (OCb l))} ⊔ Ideal.span {bk.ev bk.E}).map (WittVector.map ψ))
      (WittVector l O) := by
  obtain ⟨w, -, hwE⟩ := GlobalTheory.T.breuilKisin_eisenstein_image_teichmuller_pow l K bk O ψ hxu
  have hE0 : WittVector.map ψ (bk.ev bk.E) ≠ 0 := fun h => by
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := O)) h
    rw [hwE, map_add (f := _), map_mul, map_pow, map_natCast, CharP.cast_eq_zero, zero_mul, add_zero,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, map_zero] at h1
    exact hx0 ((pow_eq_zero_iff bk.deg_pos.ne').1 h1)
  refine ⟨mem_nonZeroDivisors_of_ne_zero hE0, isHausdorff_of_le_ideal ?_
    (GlobalTheory.T.wittVector_teichmuller_isAdicComplete_of_perfect l O (ψ bk.flat) hx0 hxc).2.toIsHausdorff⟩
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_natCast]
  refine sup_le le_sup_left ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hwE]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ bk.deg_pos))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

theorem isHausdorff_map_congr {A B : Type} [CommRing A] [CommRing B] {I J : Ideal A} {g h : A →+* B} (hIJ : I = J)
    (hgh : g = h) (H : IsHausdorff (J.map h) B) : IsHausdorff (I.map g) B := by
  subst hIJ; subst hgh; exact H

theorem envPoint_eq {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X))
    (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (ψ : OCb l →+* O)
    (hx0 : ψ bk.flat ≠ 0) (hxu : ¬ IsUnit (ψ bk.flat)) (hxc : IsAdicComplete (Ideal.span {ψ bk.flat}) O)
    (F : En.Q.A →+* WittVector l O) (hFφ : ∀ a, F (En.Q.D.φ a) = WittVector.frobenius (F a))
    (hFinl : F.comp En.inl.f = WittVector.map ψ) (s : Hom En.Q (ainfObj K)) (hs1 : s.comp En.inl = Hom.id _)
    (hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X))) (a : En.Q.A) :
    F a = WittVector.map ψ (s.f a) := by
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b
  have htfW : ∀ c : WittVector l O, ((l : ℕ) : WittVector l O) * c = 0 → c = 0 := fun c hc =>
    WittVector.eq_zero_of_p_mul_eq_zero c (by rw [mul_comm, hc])
  obtain ⟨F', hF'a⟩ : ∃ F' : En.Q.A →+* WittVector l O, ∀ a, F' a = WittVector.map ψ (s.f a) :=
    ⟨(WittVector.map ψ).comp s.f, fun _ => rfl⟩
  have hF'φ : ∀ a, F' (En.Q.D.φ a) = WittVector.frobenius (F' a) := fun a =>
    ((hF'a _).trans (congrArg (WittVector.map ψ) (Hom.f_φ s a))).trans
      ((map_frobenius_charP ψ (s.f a)).trans (congrArg WittVector.frobenius (hF'a a).symm))
  have hinl : ∀ b, F (En.inl.f b) = F' (En.inl.f b) := fun b =>
    (hFi b).trans ((congrArg (WittVector.map ψ) (hom_eq_id_apply s En.inl hs1 b).symm).trans (hF'a _).symm)
  have hE := (mapE_facts bk O ψ hx0 hxu hxc).1
  have hH := (mapE_facts bk O ψ hx0 hxu hxc).2
  have hnzd : F (En.inl.f (bk.ev bk.E)) ∈ nonZeroDivisors (WittVector l O) := by
    rw [hFi]; exact hE
  have hI : (ainfObj K).I = Ideal.span {bk.ev bk.E} := bk.span_ev.symm
  have hhaus : IsHausdorff ((Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ (ainfObj K).I).map (F.comp En.inl.f))
      (WittVector l O) :=
    isHausdorff_map_congr (congrArg (Ideal.span {((l : ℕ) : (ainfObj K).A)} ⊔ ·) hI) hFinl hH
  have hFF : F = F' :=
    GlobalTheory.T.breuilKisinPrismCoproduct_hom_eq_of_agree l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) En (WittVector l O) WittVector.frobenius F F'
      htfW hFφ hF'φ hinl (hinr.trans (hF'a _).symm) hnzd hhaus
  rw [hFF, hF'a]

theorem envPoint_factors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O]
    [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 →
    ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O →
    ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧
      s.comp En.inr = (ainfHom K g).comp bk.ι ∧
      ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  intro l _ K bk En O _ _ _ _ _ f hx0 hxu hxc
  have hcc : Function.Surjective (WittVector.constantCoeff (p := l) (R := OCb l)) := fun y =>
    ⟨WittVector.teichmuller l y, by rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  let f0 : WittVector l (OCb l) →+* O := f.comp En.inl.f
  have hker : RingHom.ker (WittVector.constantCoeff (p := l) (R := OCb l)) ≤ RingHom.ker f0 := by
    rw [WittVector.ker_constantCoeff, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
      map_natCast, CharP.cast_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : OCb l →+* O, ∀ a : WittVector l (OCb l), f (En.inl.f a) = ψ (a.coeff 0) :=
    ⟨RingHom.liftOfSurjective _ hcc ⟨f0, hker⟩, fun a =>
      (RingHom.liftOfSurjective_comp_apply _ hcc ⟨f0, hker⟩ a).symm⟩
  have hflat : f (En.inl.f (bk.ev X)) = ψ bk.flat := by
    rw [hψ, bk.ev_X, WittVector.teichmuller_coeff_zero]
  rw [hflat] at hx0 hxu hxc
  obtain ⟨htf, -, -⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  obtain ⟨F, hF0, hFφ⟩ := GlobalTheory.T.exists_frobenius_compatible_wittVector_lift l En.Q.A En.Q.D.φ
    (fun a => ⟨En.Q.D.δ a, by rw [En.Q.D.φ_eq]; ring⟩) htf O f
  have hFinl : F.comp En.inl.f = WittVector.map ψ :=
    GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero l (OCb l) O (F.comp En.inl.f) ψ (fun a => (hF0 (En.inl.f a)).trans (hψ a))
  have hFi : ∀ b : WittVector l (OCb l), F (En.inl.f b) = WittVector.map ψ b := fun b => RingHom.congr_fun hFinl b

  have hφX : En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr X ^ l :=
    calc En.Q.D.φ (BK.hf En.inr X) = BK.hf En.inr (frobS l bk.a X) := (Hom.f_φ En.inr X).symm
      _ = BK.hf En.inr (X ^ l) := by rw [frobS_X]
      _ = _ := map_pow _ _ _
  set v := F (BK.hf En.inr X) with hvdef
  have hv : WittVector.frobenius v = v ^ l := by
    rw [hvdef, ← hFφ, hφX, map_pow]
  have hvt := GlobalTheory.T.wittVector_eq_teichmuller_of_frobenius_eq_pow_self l O v hv
  have e1 : F (En.inl.f (bk.ev X)) = WittVector.teichmuller l (ψ bk.flat) := by
    rw [hFi, bk.ev_X, WittVector.map_teichmuller]
  have e2 : F (En.inl.f (bk.ev bk.E)) = WittVector.map ψ (bk.ev bk.E) := hFi _
  have h1 : v = F (En.inl.f (bk.ev X)) + F (En.inl.f (bk.ev bk.E)) * F En.w := by
    have := congrArg F En.w_eq
    rwa [map_add, map_mul] at this
  rw [e1, e2] at h1
  have hdvd : WittVector.map ψ (bk.ev bk.E) ∣
      WittVector.teichmuller l (v.coeff 0) - WittVector.teichmuller l (ψ bk.flat) :=
    ⟨F En.w, by rw [← hvt]; linear_combination h1⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_galois_conj_of_teichmuller_congr l K bk O ψ hx0 hxu hxc (v.coeff 0) hdvd
  obtain ⟨s, ⟨hs1, hs2⟩, -⟩ := En.univ (ainfObj K) (Hom.id _) ((ainfHom K g).comp bk.ι)

  have hinr : F (BK.hf En.inr X) = WittVector.map ψ (s.f (BK.hf En.inr X)) := by
    have h2 : s.f (BK.hf En.inr X) = Per.σA (g : GQ l) (bk.ev X) :=
      hom_eq_comp_apply s En.inr _ _ hs2 X
    have h3 : WittVector.map ψ (Per.σA (g : GQ l) (bk.ev X)) =
        WittVector.teichmuller l (ψ (Per.σF (g : GQ l) bk.flat)) := by
      rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, WittVector.map_teichmuller]
    refine Eq.trans ?_ ((congrArg (WittVector.map ψ) h2).trans h3).symm
    exact hvdef.symm.trans (hvt.trans (congrArg (WittVector.teichmuller l) hg))
  refine ⟨g, s, ψ, hs1, hs2, fun a => ?_⟩
  rw [← hF0, envPoint_eq bk En O ψ hx0 hxu hxc F hFφ hFinl s hs1 hinr a]
  exact WittVector.map_coeff ψ (s.f a) 0

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopePointFactorsThroughSectionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : En.Q.A →+* O), f (En.inl.f (bk.ev X)) ≠ 0 → ¬ IsUnit (f (En.inl.f (bk.ev X))) → IsAdicComplete (Ideal.span {f (En.inl.f (bk.ev X))}) O → ∃ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)) (ψ : OCb l →+* O), s.comp En.inl = Hom.id _ ∧ s.comp En.inr = (ainfHom K g).comp bk.ι ∧ ∀ a, f a = ψ (WittVector.coeff (p := l) (R := OCb l) (s.f a) 0) := by
  first | exact @GlobalTheory.BSP.envPoint_factors | exact GlobalTheory.BSP.envPoint_factors | (intros; apply GlobalTheory.BSP.envPoint_factors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSections
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP


set_option maxHeartbeats 1000000 in
theorem l_dvd_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hx hs
  obtain ⟨-, -, -, -, -, -, hA7⟩ := GlobalTheory.T.ainf_divisibility_breuilKisin_facts l K bk
  obtain ⟨-, hM2, hM3⟩ := GlobalTheory.T.ainf_envelope_mod_prime_properties l K bk En
  let I : Ideal En.Q.A := Ideal.span {((l : ℕ) : En.Q.A)}
  let π : En.Q.A →+* En.Q.A ⧸ I := Ideal.Quotient.mk I
  have hπ : ∀ y, π y = 0 ↔ ((l : ℕ) : En.Q.A) ∣ y := fun y =>
    Ideal.Quotient.eq_zero_iff_mem.trans Ideal.mem_span_singleton
  have hl0 : ((l : ℕ) : En.Q.A ⧸ I) = 0 := by
    rw [← map_natCast π]; exact (hπ _).2 dvd_rfl
  have hreg : π (En.inl.f (bk.ev X)) ∈ nonZeroDivisors (En.Q.A ⧸ I) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    have : π (En.inl.f (bk.ev X) * y) = 0 := by rw [map_mul, mul_comm]; exact hy
    exact (hπ _).2 (hM2 y ((hπ _).1 this))
  have hE : π (En.inl.f (bk.ev bk.E)) = π (En.inl.f (bk.ev X)) ^ bk.Ep.natDegree := by
    let ι : Ainf l →+* En.Q.A := En.inl.f
    have h1 : ((l : ℕ) : En.Q.A) ∣ ι (bk.ev bk.E - bk.ev X ^ bk.Ep.natDegree) := by
      have := map_dvd ι hA7
      rwa [map_natCast] at this
    have h2 := (hπ _).2 h1
    rw [map_sub, map_pow, map_sub, map_pow, sub_eq_zero] at h2
    exact h2
  have hl1 : π ((l : ℕ) : En.Q.A) = 0 := (hπ _).2 dvd_rfl
  have hφ : ∀ y, π (En.Q.D.φ y) = π y ^ l := fun y => by
    have e : π (En.Q.D.φ y - y ^ l) = 0 := (hπ _).2 ⟨En.Q.D.δ y, by rw [En.Q.D.φ_eq y]; ring⟩
    rwa [map_sub, map_pow, sub_eq_zero] at e
  have heq : ∀ j, π (En.inl.f (bk.ev X)) ^ (bk.Ep.natDegree * h) * π (x j) =
      ∑ i, π (x i) ^ l * π (c i j) := fun j => by
    have := congrArg π (hx j)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul π, map_pow π, hE, ← pow_mul, map_sum π] at this
    rw [this]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul π, hφ]
  have hpts : ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l]
      (f : En.Q.A ⧸ I →+* O), f (π (En.inl.f (bk.ev X))) ≠ 0 → ¬ IsUnit (f (π (En.inl.f (bk.ev X)))) →
      IsAdicComplete (Ideal.span {f (π (En.inl.f (bk.ev X)))}) O → ∀ j, f (π (x j)) = 0 := by
    intro O _ _ _ _ _ f hf0 hfu hfc j
    obtain ⟨g, s, ψ, h1, h2, h3⟩ := GlobalTheory.T.breuilKisinEnvelope_point_factors_through_section l K bk En O (f.comp π) hf0 hfu hfc
    obtain ⟨z, hz⟩ := hs g s h1 h2 j
    have e := h3 (x j)
    rw [RingHom.comp_apply] at e
    rw [e, hz]
    have : WittVector.coeff (p := l) (R := OCb l) (((l : ℕ) : (ainfObj K).A) * z) 0 = 0 := by
      rw [mul_comm]; exact WittVector.mul_charP_coeff_zero (p := l) (R := OCb l) z
    rw [this, map_zero]
  have key := GlobalTheory.T.dvd_all_pow_of_frobenius_eq_killed_by_perfect_points l (En.Q.A ⧸ I) (π (En.inl.f (bk.ev X))) hl0 hreg κ (fun i => π (x i))
    (fun i j => π (c i j)) (bk.Ep.natDegree * h) heq (fun O _ _ _ _ _ f hf0 hfu hfc j => hpts O f hf0 hfu hfc j)
  intro j
  refine hM3 (x j) fun m => ?_
  obtain ⟨w, hw⟩ := key m j
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨z, (hπ _).1 ?_⟩
  change π (x j) = π (En.inl.f (bk.ev X)) ^ m * π z at hw
  rw [map_sub π, map_mul π, map_pow π, hw, sub_self]

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimeDvdAinfEnvelopeOfGaloisSectionsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_dvd_ainfEnvelope_of_galois_sections : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, En.inl.f (bk.ev bk.E) ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (s : Hom En.Q (ainfObj K)), s.comp En.inl = Hom.id _ → s.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.l_dvd_of_galois_sections | exact GlobalTheory.BSP.l_dvd_of_galois_sections | (intros; apply GlobalTheory.BSP.l_dvd_of_galois_sections <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproduct
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem ringHom_map_sum' {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {ι : Type} (s : Finset ι)
    (g : ι → A) : f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) := map_sum f g s


set_option maxHeartbeats 400000 in
theorem dvd_l_of_sections_env_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  intro l _ K bk En κ _ x c h hrel hsec j
  have hfr : IsFrame bk (ainfObj K) (bk.ev bk.E) (bk.ev X) := by
    have := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk (ainfObj K) bk.ι
    rwa [show BK.hf bk.ι = bk.ev from rfl] at this
  have hAn := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk (ainfObj K) (bk.ev bk.E) (bk.ev X) hfr
  obtain ⟨An⟩ := hAn
  obtain ⟨q, ⟨hq1, hq2⟩, -⟩ := En.univ An.Q (An.inl.comp bk.ι) An.inr
  have hE : q.f (BK.hf En.inl bk.E) = An.inl.f (bk.ev bk.E) := by
    change (q.comp En.inl).f bk.E = _
    rw [hq1]; rfl
  have hrel' : ∀ j, An.inl.f (bk.ev bk.E) ^ h * q.f (x j) = ∑ i, An.Q.D.φ (q.f (x i)) * q.f (c i j) := by
    intro j
    have t1 : q.f (BK.hf En.inl bk.E ^ h * x j) = q.f (BK.hf En.inl bk.E ^ h) * q.f (x j) := q.f.map_mul _ _
    have t2 : q.f (BK.hf En.inl bk.E ^ h) = An.inl.f (bk.ev bk.E) ^ h := (q.f.map_pow _ _).trans (congrArg (· ^ h) hE)
    have t3 : q.f (BK.hf En.inl bk.E ^ h * x j) = An.inl.f (bk.ev bk.E) ^ h * q.f (x j) :=
      t1.trans (congrArg (fun t : An.Q.A => t * q.f (x j)) t2)
    have e2a := ringHom_map_sum' q.f Finset.univ (fun i => En.Q.D.φ (x i) * c i j)
    have e2b : ∀ i, q.f (En.Q.D.φ (x i) * c i j) = An.Q.D.φ (q.f (x i)) * q.f (c i j) := fun i =>
      (q.f.map_mul _ _).trans (congrArg (fun t : An.Q.A => t * q.f (c i j)) (Hom.f_φ q (x i)))
    have e2c := Finset.sum_congr (s₁ := (Finset.univ : Finset κ)) rfl (fun i (_ : i ∈ Finset.univ) => e2b i)
    have e3 := congrArg q.f (hrel j)
    exact t3.symm.trans (e3.trans (e2a.trans e2c))
  have hsec' : ∀ (g : ↥(GK K)) (s : Hom An.Q (ainfObj K)), s.comp An.inl = Hom.id _ →
      s.comp An.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ s.f (q.f (x j)) := by
    intro g s hs1 hs2 j
    have h1 : (s.comp q).comp En.inl = bk.ι := by
      have : (s.comp q).comp En.inl = (s.comp An.inl).comp bk.ι := by
        rw [show (s.comp q).comp En.inl = s.comp (q.comp En.inl) from Hom.ext' rfl, hq1]
        exact Hom.ext' rfl
      rw [this, hs1]; exact Hom.ext' rfl
    have h2 : (s.comp q).comp En.inr = (ainfHom K g).comp bk.ι := by
      rw [show (s.comp q).comp En.inr = s.comp (q.comp En.inr) from Hom.ext' rfl, hq2, hs2]
    exact hsec g (s.comp q) h1 h2 j
  have key := GlobalTheory.T.prime_dvd_ainfEnvelope_of_galois_sections l K bk An κ (fun i => q.f (x i)) (fun i k => q.f (c i k)) h hrel' hsec'
  exact GlobalTheory.T.breuilKisin_envelope_dvd_prime_of_ainf l K bk En An q hq1 hq2 (x j) (key j)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdLOfGaloisSectionsBreuilKisinCoproductStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_l_of_galoisSections_breuilKisinCoproduct : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (κ : Type) [Fintype κ] (x : κ → En.Q.A) (c : κ → κ → En.Q.A) (h : ℕ), (∀ j, BK.hf En.inl bk.E ^ h * x j = ∑ i, En.Q.D.φ (x i) * c i j) → (∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι → σ.comp En.inr = (ainfHom K g).comp bk.ι → ∀ j, ((l : ℕ) : (ainfObj K).A) ∣ σ.f (x j)) → ∀ j, ((l : ℕ) : En.Q.A) ∣ x j := by
  first | exact @GlobalTheory.BSP.dvd_l_of_sections_env_bk | exact GlobalTheory.BSP.dvd_l_of_sections_env_bk | (intros; apply GlobalTheory.BSP.dvd_l_of_sections_env_bk <;> assumption)
end
