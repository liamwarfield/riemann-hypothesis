module

public import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCm
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneVectorOfMultiplicityOne
noncomputable section

open Module NumberField
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

namespace GlobalTheory.OneForm

section GroupAlgebra

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]


open Classical in
def typeSum (P : Subgroup G) (ψ : P →* Kˣ) (χ : G → K) : K := ∑ h : P, χ (h : G) * (((ψ h)⁻¹ : Kˣ) : K)

end GroupAlgebra

section Modules

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]
  {V : Type} [AddCommGroup V] [Module K V]

omit [CharZero K] in
theorem asAlg_eq_sum (r : Representation K G V) (a : MonoidAlgebra K G) (x : V) :
    r.asAlgebraHom a x = ∑ g : G, a.coeff g • r g x := by
  conv_lhs => rw [eq_sum_single a]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, LinearMap.sum_apply]



end Modules

section Coordinates

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem range_toF {G : Type} [Group G] [Fintype G] {Pl0 : Type} (B : BlockDat K G Pl0) (ℓ : Lvl K G)
    (Z : Submodule K B.S.Forms) :
    LinearMap.range (B.toF ℓ Z) = Z ⊓ LinearMap.range (B.r.asAlgebraHom (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  have hop : ∀ (a : MonoidAlgebra K G) (φ : B.S.Forms), B.S.gaOp B.r a φ = B.r.asAlgebraHom a φ := by
    intro a φ
    rw [asAlg_eq_sum, CSD.gaOp, LinearMap.sum_apply]
    rfl
  have hV : LinearMap.range (B.vE ℓ).mulVecLin =
      LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin :=
    (image_idempotent_spec K B.S.dim (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
  ext φ
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨(B.mem_goodPart_iff ℓ Z _).1 (B.zE_mem ℓ Z y), ?_⟩
    have : (B.vE ℓ).mulVec ((B.zE ℓ Z).mulVec y) ∈ LinearMap.range (B.vE ℓ).mulVecLin := ⟨_, rfl⟩
    rw [hV] at this
    obtain ⟨u, hu⟩ := this
    refine ⟨B.S.basis.equivFun.symm u, ?_⟩
    rw [B.toF_apply, ← hu, ← hop, LinearEquiv.eq_symm_apply, ← CSD.gaMat_mulVec_equivFun,
      LinearEquiv.apply_symm_apply]
    rfl
  · rintro ⟨hZ, w, hw⟩
    have : B.S.basis.equivFun φ ∈ LinearMap.range (B.vE ℓ).mulVecLin := by
      rw [hV]
      refine ⟨B.S.basis.equivFun w, ?_⟩
      rw [Matrix.mulVecLin_apply, CSD.gaMat_mulVec_equivFun, hop, hw]
    obtain ⟨u, hu⟩ := this
    rw [Matrix.mulVecLin_apply] at hu
    have hu0 : u ∈ B.Z0 ℓ Z := by
      rw [BlockDat.Z0, B.mem_goodPart_iff, hu, LinearEquiv.symm_apply_apply]
      exact hZ
    obtain ⟨y, hy⟩ := B.exists_zE ℓ Z hu0
    exact ⟨y, by rw [B.toF_apply, hy, hu, LinearEquiv.symm_apply_apply]⟩

variable {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A) {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool)

theorem iC_cpt (t : Bs.Tup) (x : Fin ((lv (fc X.zs) b).dQ t) → K) :
    X.iC cr b t (cpt Bs.v0.embedding x) = X.Θ t (X.jR t (cr.toR X.zs b t x)) := by
  classical
  conv_rhs => rw [← Finset.univ_sum_single x]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [CxData.iC, lin_apply, map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (Pi.single k (x k) : Fin _ → K) = x k • Pi.single k 1 := by
    funext i; by_cases hi : i = k <;> simp [hi]
  rw [this, map_smul, map_smulₛₗ, map_smul]
  rfl

end Coordinates

section Family

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn K G Pl0 T m}

def OneVector (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) : Prop :=
  ∀ χ ∈ X, typeSum P ψ χ = (Nat.card P : K)

section Faces

variable (X : CxData A.fam.amb) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
  (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
  (Zsc : DefSub A.fam.amb → IndefScale A.fam.base)

end Faces

end Family

section Concrete

open Formalism.BasicNotions Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def rowSub (R : RealDat D A Ks) (t : T) : Submodule D.what₂.LL (A.fam.amb.FR t) :=
  (LinearMap.range (LinearMap.adjoint (Tw.map (twAt D.what₂.embLL A.v0) (R.Th t)))).comap
    (Tw.semi (σ' := A.v0.embedding) (twAt D.what₂.embLL A.v0) R.emb0 (R.jX t))

def GoodInduced (R : RealDat D A Ks) : Prop :=
  ∀ χ ∈ A.X, GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.IsCuspIndProdChar R.Pg D.R.r D.what₂.embLL fun g => χ (R.eG.symm g)

theorem oneVector_of_whittaker (R : RealDat D A Ks) (F : Face D A) (hW : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector)
    (hlev : R.grp_levels F) (hind : GoodInduced R) : OneVector A.X F.P0 F.ψ0 := by
  classical
  obtain ⟨ψ, hψ, hP, -⟩ := hlev
  intro χ hχ
  have h := hW D.host.E R.Pg D.R.r ℂ (RingHom.id ℂ) ψ hψ (fun g => D.what₂.embLL (χ (R.eG.symm g))) (hind χ hχ)
  rw [← hP] at h
  let e : (R.levR F false).H ≃ F.P0 := R.eG.symm.toEquiv.subtypeEquiv fun _ => Iff.rfl
  apply D.what₂.embLL.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_natCast, ← Nat.card_congr e, ← h, typeSum, map_sum]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.lvlSum
  letI := GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.fintypeH (R.levR F false)
  refine (Fintype.sum_equiv e _ _ fun x => ?_).symm
  rw [map_mul]
  rfl

end Concrete

end GlobalTheory.OneForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlace
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitIndex

open GlobalTheory.SplitScalar

variable {D : D7}

theorem finPart_cA_eq_zero {a : AE D} (h : finPart D a = 0) : finPart D (cA D a) = 0 := by
  rw [← realIdem_mul_of_real h, RingHom.map_mul, cA_realIdem, RingHom.map_mul, finPart_realIdem, zero_mul]

theorem tmul_split {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (β : Af F) (x : F) (k : ℕ) (t : E) :
    (algebraMap F (Af F) x + k • β) ⊗ₜ[F] t =
      (1 : Af F) ⊗ₜ[F] (algebraMap F E x * t) + k • (β ⊗ₜ[F] t) := by
  rw [TensorProduct.add_tmul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one x,
    TensorProduct.smul_tmul, Algebra.smul_def x t]

theorem map_add_nsmul {A B : Type} [Ring A] [Ring B] (f : A →+* B) (k : ℕ) (a s : A) :
    f (a + k • s) = f a + k • f s := by rw [map_add (f := _), map_nsmul]

theorem zero_eq_map_add_nsmul_zero {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) :
    0 = f (g 0 + k • 0) := by simp

theorem add_nsmul_residue_add {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r r' : E)
    (s s' : A) : f (g r + k • s) + f (g r' + k • s') = f (g (r + r') + k • (s + s')) := by
  rw [← map_add (f := _), map_add g, smul_add]; congr 1; abel

theorem neg_nsmul_residue {E A B : Type} [Ring E] [Ring A] [Ring B] (g : E →+* A) (f : A →+* B) (k : ℕ) (r : E)
    (s : A) : -f (g r + k • s) = f (g (-r) + k • (-s)) := by
  rw [← map_neg, map_neg g, smul_neg, neg_add]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) :
    ∃ (r : 𝓞 D.host.E) (s : AE D), finPart D s ∈ intAE D ∧ finPart D (cA D s) ∈ intAE D ∧
      z = finPart D (incA D (r : D.host.E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, t, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat D.host.F k hk).2 α hα
    refine ⟨algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x * t, pairA D.host.F 0 β ⊗ₜ[D.host.F] (t : D.host.E),
      AddSubgroup.subset_closure ⟨β, hβ, t, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, GlobalTheory.FinWeil.sgO D t, ?_⟩, ?_⟩
    · rw [GlobalTheory.FinWeil.coe_sgO, ← GlobalTheory.SplitIdem.star_eq_conj]
      rfl
    · rw [hx]
      refine Eq.trans ?_ (map_add_nsmul (finPart D) k _ _).symm
      exact tmul_split β (x : D.host.F) k (t : D.host.E)
  | zero => exact ⟨0, 0, by rw [RingHom.map_zero]; exact zero_mem _,
      by rw [RingHom.map_zero, RingHom.map_zero]; exact zero_mem _,
      zero_eq_map_add_nsmul_zero (incA D) (finPart D) k⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [RingHom.map_add (f := _)]; exact add_mem h1 h1',
      by rw [RingHom.map_add (f := _), RingHom.map_add (f := _)]; exact add_mem h2 h2', ?_⟩
    exact add_nsmul_residue_add (incA D) (finPart D) k _ _ s s'
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [RingHom.map_neg]; exact neg_mem h1,
      by rw [RingHom.map_neg, RingHom.map_neg]; exact neg_mem h2, ?_⟩
    exact neg_nsmul_residue (incA D) (finPart D) k _ s

theorem core_mem {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (hΛ : ∀ r : O, ∀ u ∈ Λ, ι r • u ∈ Λ) (q : ℕ) (y : M) (hq : q • y ∈ Λ) (r r' : O)
    (h1 : ι (1 - r) • y ∈ Λ) (h2 : ι r' • y ∈ Λ)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : y ∈ Λ := by
  let I : Ideal O :=
    { carrier := {a | ι a • y ∈ Λ}
      add_mem' := fun {a b} ha hb => by
        show ι (a + b) • y ∈ Λ
        rw [map_add (f := _), add_smul]; exact add_mem ha hb
      zero_mem' := by
        show ι 0 • y ∈ Λ
        rw [map_zero, zero_smul]; exact zero_mem _
      smul_mem' := fun c a ha => by
        show ι (c * a) • y ∈ Λ
        rw [map_mul, mul_smul]; exact hΛ c _ ha }
  by_contra hy
  have hI : I ≠ ⊤ := fun h => by
    have : (1 : O) ∈ I := by rw [h]; trivial
    exact hy (by simpa [I] using this)
  obtain ⟨P, hPm, hIP⟩ := Ideal.exists_le_maximal I hI
  have hqI : (q : O) ∈ I := by
    show ι (q : O) • y ∈ Λ
    rw [map_natCast, Nat.cast_smul_eq_nsmul]; exact hq
  have hr := hP P hPm (hIP hqI) (hIP h2)
  have := add_mem (hIP h1 : 1 - r ∈ P) hr
  rw [sub_add_cancel] at this
  exact hPm.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem wachExpansion_smul_compatible {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (q : ℕ) (e f b s : A) (x : M)
    (h : (f - (b + q • s)) * e = 0) : b • e • x = (f * e) • x - s • e • q • x := by
  have : b * e = f * e - s * e * q := by
    rw [nsmul_eq_mul] at h
    linear_combination -h
  rw [smul_smul, this, sub_smul, mul_smul (s * e), mul_smul s, Nat.cast_smul_eq_nsmul]

theorem core_split {O A M : Type} [CommRing O] [CommRing A] [AddCommGroup M] [Module A M] (ι : O →+* A)
    (Λ : AddSubgroup M) (p : A → Prop) (hΛ : ∀ a, p a → ∀ u ∈ Λ, a • u ∈ Λ) (hι : ∀ r, p (ι r)) (q : ℕ) (x : M)
    (hx : q • x ∈ Λ) (e f s s' : A) (he : p e) (hs : p s) (hs' : p s') (hee : e * e = e) (hef : e * f = 0)
    (r r' : O) (h1 : (e - (ι r + q • s)) * e = 0) (h2 : (f - (ι r' + q • s')) * e = 0)
    (hP : ∀ P : Ideal O, P.IsMaximal → (q : O) ∈ P → r' ∈ P → r ∈ P) : e • x ∈ Λ := by
  have hqe : e • q • x ∈ Λ := hΛ e he _ hx
  refine core_mem ι Λ (fun a => hΛ _ (hι a)) q (e • x) (by rw [smul_comm]; exact hqe) r r' ?_ ?_ hP
  · rw [map_sub, map_one, sub_smul, one_smul, wachExpansion_smul_compatible q e e _ s x h1, hee, sub_sub_cancel]
    exact hΛ s hs _ hqe
  · rw [wachExpansion_smul_compatible q e f _ s' x h2, mul_comm, hef, zero_smul, zero_sub]
    exact neg_mem (hΛ _ hs' _ hqe)

theorem mem_of_inert {q : ℕ} (hq : q.Prime) (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) (r : 𝓞 D.host.E)
    (P : Ideal (𝓞 D.host.E)) (hP : P.IsMaximal) (hqP : (q : 𝓞 D.host.E) ∈ P) (hr : GlobalTheory.FinWeil.sgO D r ∈ P) :
    r ∈ P := by
  have hne : P ≠ ⊥ := fun h => by
    rw [h, Ideal.mem_bot] at hqP
    exact hq.ne_zero (by exact_mod_cast hqP)
  have hc := hin P hP.isPrime hne hqP
  rw [← hc] at hr
  exact Ideal.smul_mem_pointwise_smul_iff.1 hr

theorem mul_splitIdem_eq_zero {e : AE D} (he : IsSplitIdem D e) {a : AE D} (ha : finPart D a = 0) : a * e = 0 :=
  adele_ext (by rw [RingHom.map_mul, infPart_splitIdem he, mul_zero, RingHom.map_zero])
    (by rw [RingHom.map_mul, ha, zero_mul, RingHom.map_zero])

theorem finPart_incA_mem (a : 𝓞 D.host.E) : finPart D (incA D (a : D.host.E)) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, a, rfl⟩

theorem split_mem {S T : HSp D} {e : AE D} (he : IsSplitIdem D e) {Λ : AddSubgroup (WO S T)}
    (hΛ : ∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) {q : ℕ} (hq : q.Prime)
    (hin : Formalism.MainNotions.StandardLatticesGL3.InertQ D q) {x : WO S T} (hx : q • x ∈ Λ) : e • x ∈ Λ := by
  have heI : finPart D e ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  obtain ⟨r, s, hs, hs', hz⟩ := approx hq.pos heI
  have h0 : finPart D (e - (incA D (r : D.host.E) + q • s)) = 0 := by rw [RingHom.map_sub, ← hz, sub_self]
  have h0' := finPart_cA_eq_zero h0
  rw [RingHom.map_sub, map_add_nsmul, GlobalTheory.DualPairCheck.cA_incA, GlobalTheory.SplitIdem.star_eq_conj,
    ← GlobalTheory.FinWeil.coe_sgO] at h0'
  exact core_split ((incA D).comp (algebraMap (𝓞 D.host.E) D.host.E)) Λ (fun a => finPart D a ∈ intAE D) hΛ
    finPart_incA_mem q x hx e (cA D e) s (cA D s) heI hs hs' he.1 he.2.1 r (GlobalTheory.FinWeil.sgO D r)
    (mul_splitIdem_eq_zero he h0) (mul_splitIdem_eq_zero he h0') (mem_of_inert hq hin r)

theorem not_dvd_of_saturated {M : Type} [AddCommGroup M] (Λ Λ' : AddSubgroup M) (h0 : Λ.relIndex Λ' ≠ 0)
    {q : ℕ} (hq : q.Prime) (h : ∀ x ∈ Λ', q • x ∈ Λ → x ∈ Λ) : ¬ q ∣ Λ.relIndex Λ' := by
  intro hdvd
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (Λ' ⧸ Λ.addSubgroupOf Λ') := Nat.finite_of_card_ne_zero h0
  obtain ⟨g, hg⟩ := exists_prime_addOrderOf_dvd_card' (G := Λ' ⧸ Λ.addSubgroupOf Λ') q hdvd
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective g
  have hqx : q • (x : M) ∈ Λ := by
    have h := addOrderOf_nsmul_eq_zero (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ')
    rw [hg, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at h
    exact h
  have h2 : (QuotientAddGroup.mk x : Λ' ⧸ Λ.addSubgroupOf Λ') = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 (h x x.2 hqx)
  rw [h2, addOrderOf_zero] at hg
  exact hq.one_lt.ne hg

theorem mem_of_parts {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (Λ : AddSubgroup M) (e f : A) (x : M)
    (h1 : e • x ∈ Λ) (h2 : f • x ∈ Λ) (h3 : (1 - (e + f)) • x ∈ Λ) : x ∈ Λ := by
  have h := add_mem (add_mem h1 h2) h3
  rwa [← add_smul, ← add_smul, add_sub_cancel, one_smul] at h

theorem not_dvd_relIndex : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  intro D S T e he Λ Λ' hΛ _ _ h1 h0 q hq hin
  exact not_dvd_of_saturated Λ Λ' h0 hq fun x hx hqx => mem_of_parts Λ e (cA D e) x
    (split_mem he hΛ hq hin hqx) (split_mem (isSplitIdem_conj he) hΛ hq hin hqx) (h1 x hx)

end GlobalTheory.SplitIndex

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimeNotDvdRelIndexSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPrime_not_dvd_relIndex_splitPlace : ∀ (D : D7) (S T : HSp D) (e : AE D), IsSplitIdem D e → ∀ Λ Λ' : AddSubgroup (WO S T), (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ, a • u ∈ Λ) → (∀ a : AE D, finPart D a ∈ intAE D → ∀ u ∈ Λ', a • u ∈ Λ') → (∀ u ∈ Λ', u.map (infPart D) = 0) → (∀ u ∈ Λ', (1 - (e + cA D e)) • u ∈ Λ) → Λ.relIndex Λ' ≠ 0 → ∀ q : ℕ, q.Prime → Formalism.MainNotions.StandardLatticesGL3.InertQ D q → ¬ q ∣ Λ.relIndex Λ' := by
  first | exact @GlobalTheory.SplitIndex.not_dvd_relIndex | exact GlobalTheory.SplitIndex.not_dvd_relIndex | (intros; apply GlobalTheory.SplitIndex.not_dvd_relIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCmStatement
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orderLattice_eq_steinitzForm_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ θ : E, θ ∉ maximalRealSubfield E → ∃ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (a₀ : maximalRealSubfield E), ∀ x : E, x ∈ lattice c y ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)), x = (a : E) + (b : E) * (θ + (a₀ : E)) := by
  first | exact @GlobalTheory.SteinitzOrder.lattice_eq_steinitz | exact GlobalTheory.SteinitzOrder.lattice_eq_steinitz | (intros; apply GlobalTheory.SteinitzOrder.lattice_eq_steinitz <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBundleQuotientEquivalence
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.KS.Leray

theorem isProper_pow_hom {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) (m : ℕ) :
    IsProper (GlobalTheory.KS.pow A m).hom :=
  GlobalTheory.FibrePowerProper.isProper_fan_pt m (fun _ => A) (fun _ => hA) (limit.cone _) (limit.isLimit _)

end GlobalTheory.KS.Leray
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResSConjGen
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResConjPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_mem_int (τ : E →ₐ[F] E) {s : E ⊗[F] Formalism.L2.Herm.Af F} (hs : s ∈ Formalism.L2.Herm.intAf F E) :
    Formalism.UG.sigR τ (Formalism.L2.Herm.Af F) s ∈ Formalism.L2.Herm.intAf F E := by
  have : Formalism.L2.Herm.intAf F E ≤ (Formalism.L2.Herm.intAf F E).comap (Formalism.UG.sigR τ (Formalism.L2.Herm.Af F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, c, rfl⟩, rfl⟩ | ⟨b, rfl⟩)
    · obtain ⟨c', hc'⟩ : ∃ y' : 𝓞 E, (y' : E) = τ (c : E) :=
        ⟨⟨τ (c : E), (c.isIntegral_coe).map ((τ : E →+* E).toIntAlgHom)⟩, rfl⟩
      refine Subring.subset_closure (Or.inl ⟨⟨_, c', rfl⟩, ?_⟩)
      show (c' : E) ⊗ₜ[F] _ = τ (c : E) ⊗ₜ[F] _
      rw [hc']; rfl
    · refine Subring.subset_closure (Or.inr ⟨b, ?_⟩)
      show _ = τ 1 ⊗ₜ[F] _
      rw [map_one]; rfl
  exact this hs

end General

end GlobalTheory.ResConjPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelf
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc

namespace GlobalTheory.LKLoc

theorem frobR_iterate_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)),
    FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  intro p _ K hK r hr x
  have hit : ∀ (i : ℕ) (y : Kn p K r),
      (((⇑(frobR p K r))^[i] y : Kn p K r) : PadicAlgCl p) = (frobK p K ^ i) (y : PadicAlgCl p) := by
    intro i
    induction i with
    | zero => intro y; rfl
    | succ i ih =>
      intro y
      rw [Function.iterate_succ_apply', pow_succ', AlgEquiv.mul_apply, ← ih]
      rfl
  apply Subtype.ext
  rw [hit]
  exact (IsFrobOn.pow_fixes_iff p K hK hr ((isFrob_frobK hK).isFrobOn r) r).2 dvd_rfl _ x.2

end GlobalTheory.LKLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedExtFrobeniusIterateDegreeEqSelfStatement
open ReciprocityTheory.DiscreteGroups.LocalClassField Matrix GlobalTheory.LKLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramifiedExtFrobenius_iterate_degree_eq_self : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (r : ℕ), 0 < r → ∀ x : Kn p K r, (⇑(frobR p K r))^[r] x = x := by
  first | exact @GlobalTheory.LKLoc.frobR_iterate_self | exact GlobalTheory.LKLoc.frobR_iterate_self | (intros; apply GlobalTheory.LKLoc.frobR_iterate_self <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhiskerLeftIsOpenImmersionRange
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem whiskerLeft_isOpenImmersion_range :
    ∀ (S : Scheme.{0}) (A T Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left →
      IsOpenImmersion (A ◁ z).left ∧ ∀ x, x ∈ Set.range (A ◁ z).left ↔ (snd A T).left x ∈ Set.range z.left := by
  intro S A T Z z hz
  have hc : pullback.snd A.hom Z.hom ≫ z.left = (A ◁ z).left ≫ pullback.snd A.hom T.hom := by
    rw [Over.whiskerLeft_left, pullback.lift_snd]
  have hsq : IsPullback (pullback.snd A.hom Z.hom) (A ◁ z).left z.left (pullback.snd A.hom T.hom) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst A.hom T.hom) (v₂₂ := T.hom) (h₃₁ := A.hom) ?_ hc
      (IsPullback.of_hasPullback A.hom T.hom).flip
    have e1 : (A ◁ z).left ≫ pullback.fst A.hom T.hom = pullback.fst A.hom Z.hom := by
      rw [Over.whiskerLeft_left, pullback.lift_fst, Category.comp_id]
    have e2 : z.left ≫ T.hom = Z.hom := Over.w z
    rw [e1, e2]
    exact (IsPullback.of_hasPullback A.hom Z.hom).flip
  have hsnd : (snd A T).left = pullback.snd A.hom T.hom := by simp
  refine ⟨?_, fun x => ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) hsq hz
  · rw [hsnd]
    constructor
    · rintro ⟨y, rfl⟩
      refine ⟨pullback.snd A.hom Z.hom y, ?_⟩
      rw [← Scheme.Hom.comp_apply, hc, Scheme.Hom.comp_apply]
    · rintro ⟨w, hw⟩
      obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback (f := z.left) (g := pullback.snd A.hom T.hom) w x hw
      refine ⟨hsq.isoPullback.inv p, ?_⟩
      rw [← Scheme.Hom.comp_apply, hsq.isoPullback_inv_snd, hp2]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSnd
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem bijective_app_iso_comp {X Y Z : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (g : Y ⟶ Z) (V : Z.Opens)
    (h : Function.Bijective (g.app V).hom) : Function.Bijective ((f ≫ g).app V).hom := by
  have : IsIso (g.app V) := (ConcreteCategory.isIso_iff_bijective _).2 h
  have : IsIso (f.app (g ⁻¹ᵁ V)) := inferInstance
  have : IsIso ((f ≫ g).app V) := by
    rw [Scheme.Hom.comp_app]; exact IsIso.comp_isIso' ‹_› ‹_›
  exact ConcreteCategory.bijective_of_isIso _

theorem fnBij_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  intro S A T _ hA V
  have e : (snd A T).left = (β_ A T).hom.left ≫ (fst T A).left := by
    rw [← Over.comp_left, braiding_hom_fst]
  have : IsIso (β_ A T).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ A T).hom))
  rw [e]
  exact bijective_app_iso_comp _ _ V
    (GlobalTheory.CubeLawCompare.bijective_app_fst GlobalTheory.SemiRigid.globalFns hA T V)

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPreimageSectionsBijectiveAbelianSchemeSndStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPreimageSectionsBijective_abelianScheme_snd : ∀ (S : Scheme.{0}) (A T : Over S) [GrpObj A], IsAbelianScheme A → FnBij (snd A T).left := by
  first | exact @GlobalTheory.PicGlue.fnBij_snd | exact GlobalTheory.PicGlue.fnBij_snd | (intros; apply GlobalTheory.PicGlue.fnBij_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVariety
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulFinite

theorem isFinite_mul : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ n : ℕ, 1 ≤ n → IsFinite (𝟙 A ^ n : A ⟶ A).left := by
  intro k _ _ B _ hB n hn1
  have hG := GlobalTheory.laws_without_cohomology.1
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hq : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn1
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (LB.isLB_pull hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩
    (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  exact GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow k _ _ B.hom _ H H m s (n ^ 2) hH hH inferInstance (by rw [hφ]; exact hs) hq hiso

end GlobalTheory.MulFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteMulByNatAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_mulByNat_abelianVariety : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, 1 ≤ n → IsFinite (𝟙 A ^ n : A ⟶ A).left := by
  first | exact @GlobalTheory.MulFinite.isFinite_mul | exact GlobalTheory.MulFinite.isFinite_mul | (intros; apply GlobalTheory.MulFinite.isFinite_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.PicGlue

theorem stalkMap_gm {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (u : Γ(X, U)ˣ) :
    Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U u) = gm (f ≫ g) z U u := by
  by_cases h : g (f z) ∈ U
  · apply Units.ext
    rw [Units.coe_map, gm_val g (f z) U h, gm_val (f ≫ g) z U h]
    exact (Scheme.Hom.germ_stalkMap_apply f _ z h _).trans rfl
  · have h' : (f ≫ g) z ∉ U := h
    simp only [gm, dif_neg h, dif_neg h', MonoidHom.one_apply, map_one]

theorem rigOn_of_triv_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X),
    (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  intro X Y e V L hV ⟨t, ht⟩
  have hle : ∀ a : L.ι, e ⁻¹ᵁ L.U a ≤ V.ι ''ᵁ (L.pull (V.ι ≫ e)).U (fun _ => a) := by
    intro a y hy
    obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y hy
    exact V.ι.apply_mem_image_iff.2 (mem_pull.2 hy)
  refine ⟨fun a => res (hle a) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => a)), ?_⟩
  intro y a b ha hb
  obtain ⟨v, rfl⟩ : y ∈ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact hV a y ha
  have key : ∀ c : L.ι, e (V.ι v) ∈ L.U c →
      gm V.ι v (e ⁻¹ᵁ L.U c) (res (hle c) (GlobalTheory.GlueLineBundle.imU V.ι _ (t.s fun _ => c))) =
        gm (𝟙 V.toScheme) v _ (t.s fun _ => c) := by
    intro c hc
    have hm : (𝟙 V.toScheme) v ∈ (L.pull (V.ι ≫ e)).U (fun _ => c) := mem_pull.2 hc
    rw [gm_res V.ι v (hle c) (show V.ι v ∈ e ⁻¹ᵁ L.U c from hc)]
    have := GlobalTheory.GlueLineBundle.gm_imU V.ι (𝟙 V.toScheme) v _ hm (t.s fun _ => c)
    rwa [Category.id_comp] at this
  have hinj : Function.Injective (Units.map (V.ι.stalkMap v).hom.toMonoidHom) :=
    Units.map_injective (asIso (V.ι.stalkMap v)).commRingCatIsoToRingEquiv.injective
  apply hinj
  rw [map_mul, stalkMap_gm, stalkMap_gm, stalkMap_gm, Category.comp_id]
  beta_reduce
  rw [key a ha, key b hb,
    (isGen_iff_germ t).1 ht v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    gm_pull_g L (V.ι ≫ e) (𝟙 V.toScheme) v (fun _ => a) (fun _ => b) (mem_pull.2 ha) (mem_pull.2 hb),
    Category.id_comp]

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackGeneratorOfTrivialOnOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullbackGenerator_of_trivial_on_open : ∀ (X Y : Scheme.{0}) (e : Y ⟶ X) (V : Y.Opens) (L : LB X), (∀ (a : L.ι) (y : Y), e y ∈ L.U a → y ∈ V) → Triv (L.pull (V.ι ≫ e)) → ∃ r : RigD e L, RigOn e L r := by
  first | exact @GlobalTheory.PicGlue.rigOn_of_triv_open | exact GlobalTheory.PicGlue.rigOn_of_triv_open | (intros; apply GlobalTheory.PicGlue.rigOn_of_triv_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisation
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff

namespace GlobalTheory.JSW

theorem map_pLoc_pFin_finGL_locGL_of_ne {E : Type} [Field E] [NumberField E] {a : ℕ}
    {v w : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (k : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) = 1 := by
  have e : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E a (locGL E a w k)) =
      GeneralLinearGroup.map (pLoc E v) (GeneralLinearGroup.map (pFin E) (finGL E a (locGL E a w k))) := by
    ext; rfl
  rw [e, pFin_finGL, pLoc_locGL_of_ne h]

theorem whit_mul_list_prod (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ) (φ) (hφV : φ ∈ π.V)
    (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ) (l : HeightOneSpectrum (𝓞 E) → Fin a → ℕ)
    (L : List (HeightOneSpectrum (𝓞 E))) (hL : L.Nodup)
    (hw : ∀ w ∈ L, (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) ∧
      HasSatGL w (π.locRep w) (Finset.univ.val.map (α w)) ∧
      (∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) ∧ IsUnifV E w (ϖ w : w.adicCompletion E)) :
    ∀ g : GA E a, (∀ w ∈ L, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1) →
      GlobalTheory.JSW.whit φ.1 (g * (L.map fun w => finGL E a (locGL E a w (diagPow (ϖ w) (l w)))).prod) =
        (L.map fun w => GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)).prod * GlobalTheory.JSW.whit φ.1 g := by
  induction L with
  | nil => intro g _; simp
  | cons w L ih =>
    intro g hg
    rw [List.nodup_cons] at hL
    have hw0 := hw w (List.mem_cons_self ..)
    have ih' := ih hL.2 (fun v hv => hw v (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.prod_cons]
    rw [← mul_assoc, ih' (g * finGL E a (locGL E a w (diagPow (ϖ w) (l w)))) ?_,
      whit_mul_locGL_diagPow E a π w (α w) hw0.1 hw0.2.1 φ hφV hw0.2.2.1 g (hg w (List.mem_cons_self ..))
        (ϖ w) hw0.2.2.2 (l w)]
    · ring
    · intro v hv
      have hne : v ≠ w := fun h => hL.1 (h ▸ hv)
      rw [map_mul, hg v (List.mem_cons_of_mem _ hv), map_pLoc_pFin_finGL_locGL_of_ne hne, one_mul]

theorem whit_mul_tl : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  intro E _ _ _ a S hψ π α hα φ hφV hφ ϖ hϖ l hl x hx
  have hmem : ∀ w ∈ l.support.toList, w ∉ S := fun w hw => hl w (Finset.mem_toList.1 hw)
  rw [tl, whit_mul_list_prod E a π α φ hφV ϖ l l.support.toList (Finset.nodup_toList _)
      (fun w hw => ⟨hψ w (hmem w hw), hα w (hmem w hw), hφ w (hmem w hw), hϖ w⟩) x
      (fun w hw => hx w (hmem w hw))]
  congr 1
  exact Finset.prod_map_toList _ _

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerMulTorusIteratedFactorisationStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_mul_torus_iterated_factorisation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w) → ∀ (π : CuspSub E a) (α : HeightOneSpectrum (𝓞 E) → Fin a → ℂˣ), (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) → ∀ φ ∈ π.V, (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) → ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin a → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := a) S, GlobalTheory.JSW.whit φ.1 (x * GlobalTheory.JSW.tl ϖ l) = (∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) * GlobalTheory.JSW.whit φ.1 x := by
  first | exact @GlobalTheory.JSW.whit_mul_tl | exact GlobalTheory.JSW.whit_mul_tl | (intros; apply GlobalTheory.JSW.whit_mul_tl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem isoOn_gm {X Z : Scheme.{0}} {W : X.Opens} {L M : LB X} {w : Cmp W L M} (hw : IsoOn W L M w) (r : Z ⟶ X)
    (y : Z) {a a' : L.ι} {b b' : M.ι} (h0 : r y ∈ W) (ha : r y ∈ L.U a) (ha' : r y ∈ L.U a') (hb : r y ∈ M.U b)
    (hb' : r y ∈ M.U b') :
    gm r y _ (w a b) * gm r y _ (M.g b b') = gm r y _ (L.g a a') * gm r y _ (w a' b') := by
  have h1 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a ⊓ M.U b) := inf_le_left
  have h2 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ M.U b ⊓ M.U b' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_right)) (inf_le_right.trans (inf_le_right.trans inf_le_right))
  have h3 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ L.U a ⊓ L.U a' :=
    le_inf (inf_le_left.trans (inf_le_right.trans inf_le_left)) (inf_le_right.trans (inf_le_right.trans inf_le_left))
  have h4 : (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) ≤ W ⊓ (L.U a' ⊓ M.U b') := inf_le_right
  have key : ∀ (T : Scheme.{0}) (f : T ⟶ X) (t : T), f t ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) →
      gm f t _ (res h1 (w a b) * res h2 (M.g b b')) = gm f t _ (w a b) * gm f t _ (M.g b b') ∧
      gm f t _ (res h3 (L.g a a') * res h4 (w a' b')) = gm f t _ (L.g a a') * gm f t _ (w a' b') :=
    fun T f t ht ↦ ⟨(map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h1 ht _) (gm_res f t h2 ht _)),
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res f t h3 ht _) (gm_res f t h4 ht _))⟩
  have e : res h1 (w a b) * res h2 (M.g b b') = res h3 (L.g a a') * res h4 (w a' b') :=
    unit_ext fun x hx ↦ (key X (𝟙 X) x hx).1.trans ((hw x (h1 hx).1 a a' b b' (h3 hx).1 (h3 hx).2 (h2 hx).1 (h2 hx).2).trans
      (key X (𝟙 X) x hx).2.symm)
  have hm : r y ∈ (W ⊓ (L.U a ⊓ M.U b)) ⊓ (W ⊓ (L.U a' ⊓ M.U b')) := ⟨⟨h0, ha, hb⟩, ⟨h0, ha', hb'⟩⟩
  exact (key Z r y hm).1.symm.trans ((congrArg (gm r y _) e).trans (key Z r y hm).2)

theorem lbIso_pull_of_isoOn (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X)
    (hw : IsoOn W L M w) (hr : ∀ z, r z ∈ W) : LBIso (L.pull r) (M.pull r) := by
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull r).U p.1 ⊓ (L.pull r).U p.2 ≤
      r ⁻¹ᵁ (W ⊓ (L.U (p.2 PUnit.unit) ⊓ M.U (p.1 PUnit.unit))) :=
    fun p y hy ↦ ⟨hr y, mem_pull.1 hy.2, mem_pull.1 hy.1⟩
  refine ⟨⟨fun p ↦ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹⟩, fun p q ↦ unit_ext fun y hy ↦ ?_⟩
  have val : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), y ∈ (M.pull r).U p.1 ⊓ (L.pull r).U p.2 →
      gm (𝟙 Z) y _ (res (le p) (pullU r _ (w (p.2 PUnit.unit) (p.1 PUnit.unit))))⁻¹ =
        (gm r y _ (w (p.2 PUnit.unit) (p.1 PUnit.unit)))⁻¹ := fun p hp ↦
    (map_inv _ _).trans (congrArg (·⁻¹) ((gm_res (𝟙 Z) y (le p) hp _).trans
      ((gm_pull (𝟙 Z) r y _ (le p hp) _).trans (by rw [Category.id_comp]))))
  have hM := gm_pull_g M r (𝟙 Z) y p.1 q.1 hy.1.1 hy.2.1
  have hL := gm_pull_g L r (𝟙 Z) y p.2 q.2 hy.1.2 hy.2.2
  rw [Category.id_comp] at hM hL
  have hd := gm_div (L.pull r) (M.pull r) (𝟙 Z) y p q hy
  have k := isoOn_gm hw r y (hr y) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2.2) (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1)
  refine (gm_res (𝟙 Z) y inf_le_left hy _).trans ((val p hy.1).trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ?_
  refine (congrArg₂ (· * ·) (hd.trans (congrArg₂ (fun u v ↦ u * v⁻¹) hM hL))
    ((gm_res (𝟙 Z) y inf_le_right hy _).trans (val q hy.2))).trans ?_
  rw [eq_mul_inv_of_mul_eq k]
  simp only [mul_inv_rev, inv_inv]
  ac_rfl

end GlobalTheory.PicGlue
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullOfIsLineBundleIsoOnOpenStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pull_of_isLineBundleIsoOnOpen : ∀ (X Z : Scheme.{0}) (W : X.Opens) (L M : LB X) (w : Cmp W L M) (r : Z ⟶ X), IsoOn W L M w → (∀ z, r z ∈ W) → LBIso (L.pull r) (M.pull r) := by
  first | exact @GlobalTheory.PicGlue.lbIso_pull_of_isoOn | exact GlobalTheory.PicGlue.lbIso_pull_of_isoOn | (intros; apply GlobalTheory.PicGlue.lbIso_pull_of_isoOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycle
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PicGlue

variable {X : Scheme.{0}} {Ix : Type}

def sigmaGlue (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) : LB X :=
  ⟨Σ i, (L i).ι, fun p ↦ (L p.1).U p.2,
    fun p q ↦ res (le_inf (inf_le_inf ((hL p.1).le p.2) ((hL q.1).le q.2)) le_rfl) (w p.1 q.1 p.2 q.2)⟩

theorem gm_sigmaGlue_g (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k))
    (hL : ∀ i, IsOn (W i) (L i)) (x : X) (p q : (sigmaGlue W L w hL).ι)
    (hp : x ∈ (L p.1).U p.2) (hq : x ∈ (L q.1).U q.2) :
    gm (𝟙 X) x _ ((sigmaGlue W L w hL).g p q) = gm (𝟙 X) x _ (w p.1 q.1 p.2 q.2) :=
  gm_res (𝟙 X) x _ (show x ∈ (L p.1).U p.2 ⊓ (L q.1).U q.2 from ⟨hp, hq⟩) _

theorem lb_glue : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  intro X Ix W L w hW hL hiso hcoc
  have hdiag : ∀ i (a : (L i).ι) (x : X), x ∈ (L i).U a → gm (𝟙 X) x _ (w i i a a) = 1 :=
    fun i a x ha ↦ mul_eq_left.1 (hcoc i i i x a a a ha ha ha)
  have hgi : ∀ i (x : X) (b b' : (L i).ι), x ∈ (L i).U b → x ∈ (L i).U b' → x ∈ W i →
      gm (𝟙 X) x _ ((L i).g b b') = gm (𝟙 X) x _ (w i i b b') := by
    intro i x b b' hb hb' hx
    have h1 := hiso i i x ⟨hx, hx⟩ b b b b' hb hb hb hb'
    have h2 : gm (𝟙 X) x _ ((L i).g b b) = 1 := mul_eq_left.1 ((hL i).coc x b b b hb hb hb)
    rw [hdiag i b x hb, _root_.one_mul, h2, _root_.one_mul] at h1
    exact h1
  have hg := gm_sigmaGlue_g W L w hL
  refine ⟨sigmaGlue W L w hL, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨fun p b ↦ res (le_inf (le_inf
    (inf_le_right.trans (inf_le_left.trans ((hL p.1).le p.2))) inf_le_left) inf_le_right) (w p.1 i p.2 b), ?_⟩⟩
  · refine eq_top_iff.2 fun x _ ↦ TopologicalSpace.Opens.mem_iSup.2 ?_
    obtain ⟨i, hi⟩ := hW x
    obtain ⟨a, ha⟩ := (hL i).cov x hi
    exact ⟨⟨i, a⟩, ha⟩
  · intro p
    refine unit_ext fun x hx ↦ ?_
    rw [gm_res (𝟙 X) x _ hx, map_one, hg x p p hx hx, hdiag p.1 p.2 x hx]
  · intro p q r
    refine unit_ext fun x hx ↦ ?_
    rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx,
      hg x p q hx.1.1 hx.1.2, hg x q r hx.1.2 hx.2, hg x p r hx.1.1 hx.2]
    exact hcoc _ _ _ x _ _ _ hx.1.1 hx.1.2 hx.2
  · intro x hx p p' b b' hp hp' hb hb'
    beta_reduce
    erw [gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p ⊓ (L i).U b) from ⟨hx, hp, hb⟩),
      gm_res (𝟙 X) x _ (show x ∈ W i ⊓ ((sigmaGlue W L w hL).U p' ⊓ (L i).U b') from ⟨hx, hp', hb'⟩),
      hg x p p' hp hp', hgi i x b b' hb hb' hx, hcoc _ _ _ x _ _ _ hp hb hb', hcoc _ _ _ x _ _ _ hp hp' hb']

end GlobalTheory.PicGlue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleGlueOfOpenCoverCocycleStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_glue_of_openCover_cocycle : ∀ (X : Scheme.{0}) (Ix : Type) (W : Ix → X.Opens) (L : Ix → LB X) (w : ∀ i k, Cmp (W i ⊓ W k) (L i) (L k)), (∀ x, ∃ i, x ∈ W i) → (∀ i, IsOn (W i) (L i)) → (∀ i k, IsoOn (W i ⊓ W k) (L i) (L k) (w i k)) → (∀ (i j k : Ix) (x : X) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b → x ∈ (L k).U c → gm (𝟙 X) x _ (w i j a b) * gm (𝟙 X) x _ (w j k b c) = gm (𝟙 X) x _ (w i k a c)) → ∃ N : LB X, N.IsLB ∧ ∀ i, ∃ v : Cmp (W i) N (L i), IsoOn (W i) N (L i) v := by
  first | exact @GlobalTheory.PicGlue.lb_glue | exact GlobalTheory.PicGlue.lb_glue | (intros; apply GlobalTheory.PicGlue.lb_glue <;> assumption)
end
end
