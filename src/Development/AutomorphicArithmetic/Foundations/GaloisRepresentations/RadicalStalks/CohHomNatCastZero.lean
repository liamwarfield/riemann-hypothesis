module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.EpsMulSub
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFinrankDeRhamQuotientCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelPrimitiveDeRhamHodge

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugate
section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrpSchemeAbsoluteFrobeniusKillsHodgeFiltration
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published.ConjugateFiltration.Test

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0)

section Kill

variable {X : Scheme.{0}} {s : X ⟶ Sp R} (T : Thick (dp0 R) s)


include hR in
theorem cast_B : (p : T.B) = 0 := by rw [← map_natCast (algebraMap R T.B), hR, map_zero]


include hR in
theorem cast_B₀ : (p : T.B₀) = 0 := by rw [← map_natCast T.π, cast_B p hR T, map_zero]

def lft : T.B₀ →+* T.B :=
  T.π.liftOfSurjective T.surj ⟨frobR p T.B (cast_B p hR T), fun a ha ↦ by
    have hJ : a ∈ T.J := (T.ker a).1 ha
    rw [RingHom.mem_ker, frobR_apply, ← T.δ.factorial_mul_dpow_eq_pow hJ]
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Fact.out : p.Prime).pos le_rfl
    rw [hc, Nat.cast_mul, cast_B p hR T, zero_mul, zero_mul]⟩

theorem lft_π (b : T.B) : lft p hR T (T.π b) = b ^ p :=
  (RingHom.liftOfRightInverse_comp_apply _ _ _ _ b).trans (frobR_apply p _ (cast_B p hR T) b)

def red : Thick (dp0 R) s :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  Thick.triv T.B₀ T.x T.w

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta : red T ⟶ h.obj T :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  Thick.trivHom (hx := T.w) (T := h.obj T)
    { lft p hR T with
      commutes' := fun r ↦ (lft_π p hR T _).trans (by
        change _ = algebraMap R T.B (frobR p R hR r)
        rw [frobR_apply, map_pow]) }
    (by
      have e : T.π.comp (lft p hR T) = frobR p T.B₀ (cast_B₀ p hR T) := RingHom.ext fun b ↦ by
        obtain ⟨b, rfl⟩ := T.surj b
        rw [RingHom.comp_apply, lft_π, frobR_apply, map_pow]
      have h0 : (p : Γ(Sp T.B₀, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_B₀ p hR T)
      change spMap (T.π.comp (lft p hR T)) ≫ T.x = T.x ≫ GlobalTheory.VB.frob X p hX
      rw [e, ← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX T.x h0])


variable {T} in
def redMap {T' : Thick (dp0 R) s} (φ : T ⟶ T') : red T ⟶ red T' :=
  letI : Algebra R T.B₀ := (T.π.comp (algebraMap R T.B)).toAlgebra
  letI : Algebra R T'.B₀ := (T'.π.comp (algebraMap R T'.B)).toAlgebra
  Thick.trivHom (hx := T.w) (T := Thick.triv T'.B₀ T'.x T'.w)
    { φ.φ₀ with commutes' := fun r ↦ (φ.comm _).trans (congrArg T'.π (φ.φ.commutes r)) } φ.pt

theorem frobenius_kills_hodge_filtration {c : FirstDeRham s} (hc : c ∈ F1 s) : h.pull1 c = 0 := by
  rw [hodgeFiltration_eq_range] at hc
  obtain ⟨f, rfl⟩ := hc
  rw [← h.cl_pullForm]
  refine H1.mk_eq_zero.2 ⟨fun T ↦ ev (T := red T) (T' := h.obj T) f.1 (eta p hR T h), ?_⟩
  funext T T' φ
  have k := Form.ev_sq f (redMap φ) (eta p hR T' h) (eta p hR T h) (h.functor.map φ) rfl rfl fun b ↦ by
    obtain ⟨b, rfl⟩ := T.surj b
    change lft p hR T' (φ.φ₀ (T.π b)) = φ.φ (lft p hR T (T.π b))
    rw [φ.comm, lft_π, lft_π, map_pow]
  exact sub_eq_of_eq_add' k

end Kill

theorem grpScheme_absoluteFrobenius_kills_hodgeFiltration (A : Over (Sp R)) [GrpObj A] (hA : (p : Γ(A.left, ⊤)) = 0)
    (m : GrpMor (dp0 R) (𝟙 _) A (dp0 R) (𝟙 _) A (frobR p R hR) (spMap (frobR p R hR))
      (GlobalTheory.VB.frob A.left p hA)) : ∀ x ∈ PrimitiveSubmodule A, m.pull x = 0 :=
  fun _ hx ↦ Subtype.ext (frobenius_kills_hodge_filtration p hR m.isMor hx)


end GlobalTheory.Published.ConjugateFiltration.Test
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugate
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConjSeq

theorem span_pull_baseChange (H : GlobalTheory.Published.AbelianDeRham.BaseChange) {R R' : Type} [CommRing R]
    [CommRing R'] (σ : R →+* R') {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A']
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A (spMap σ) φ) {g : ℕ} (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) :
    Submodule.span R' (Set.range (GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull) = ⊤ ∧
      PrimitiveSubmodule A' = Submodule.span R' ((GlobalTheory.PDiv.grpMor_of_isGrpPullback h).pull '' PrimitiveSubmodule A) := by
  letI := σ.toAlgebra
  obtain ⟨hbc, hF⟩ := H R A g hA hg R' A' φ h
  refine ⟨Submodule.eq_top_iff'.2 fun x ↦ ?_, hF⟩
  obtain ⟨z, rfl⟩ := hbc.2 x
  induction z with
  | add a b ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
  | tmul r c => rw [liftSemi_tmul]; exact Submodule.smul_mem _ r (Submodule.subset_span ⟨c, rfl⟩)

theorem range_primPull_relFrob : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  intro H p _ R _ hR A A₁ _ _ π hπ F _ hF g hA hg
  obtain ⟨h1, h2⟩ := span_pull_baseChange H _ hπ hA hg
  have key : ∀ c, primPull (dp0 R) (𝟙 _) F ((GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ).pull c) =
      frobDR p R hR A c := fun c ↦
    GrpMor.pull_pull (GlobalTheory.PDiv.grpMor_of_isGrpPullback hπ) (homMor (dp0 R) (𝟙 _) F)
      (frobMor p R hR A (cast_left p R hR A)) (fun _ ↦ rfl) hF c
  refine ⟨?_, ?_⟩
  · rw [LinearMap.range_eq_map, ← h1, Submodule.map_span, ← Set.range_comp, conjDR]
    congr 1
    ext x
    simp only [Set.mem_range, Function.comp_apply, key]
  · rw [h2, Submodule.span_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, key]
    exact GlobalTheory.Published.ConjugateFiltration.Test.grpScheme_absoluteFrobenius_kills_hodgeFiltration p hR A (cast_left p R hR A)
      (frobMor p R hR A (cast_left p R hR A)) c hc

end GlobalTheory.ConjSeq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeRelativeFrobeniusPrimitiveDeRhamEqConjugateStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate : GlobalTheory.Published.AbelianDeRham.BaseChange → ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (A A₁ : Over (Sp R)) [GrpObj A] [GrpObj A₁] (π : A₁.left ⟶ A.left) (hπ : IsGrpPullback A₁ A (spMap (frobR p R hR)) π) (F : A ⟶ A₁) [IsMonHom F] (hF : F.left ≫ π = GlobalTheory.VB.frob A.left p (cast_left p R hR A)) (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → LinearMap.range (primPull (dp0 R) (𝟙 _) F) = conjDR p R hR A ∧ PrimitiveSubmodule A₁ ≤ LinearMap.ker (primPull (dp0 R) (𝟙 _) F) := by
  first | exact @GlobalTheory.ConjSeq.range_primPull_relFrob | exact GlobalTheory.ConjSeq.range_primPull_relFrob | (intros; apply GlobalTheory.ConjSeq.range_primPull_relFrob <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.FinrankWPow
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.Ord.DimsAlg

variable {k : Type} [Field k] {C : Type} [CommRing C]

private abbrev W (ν : C → k) : Submodule k (k ⊗[ℤ] C) :=
  ⨅ c : C, (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
    (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c).maxGenEigenspace (ν c)

private theorem mem_W (ν : C → k) (x : k ⊗[ℤ] C) :
    x ∈ W ν ↔ ∀ c : C, ∃ n : ℕ, (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n) * x = 0 := by
  simp only [W, Submodule.mem_iInf, Module.End.mem_maxGenEigenspace]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : (((Algebra.lmul k (k ⊗[ℤ] C)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] k ⊗[ℤ] C).toRingHom) c - ν c • (1 : Module.End k (k ⊗[ℤ] C)))
      = Algebra.lmul k (k ⊗[ℤ] C) ((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) := by
    have : ν c ⊗ₜ[ℤ] (1 : C) = ν c • (1 : k ⊗[ℤ] C) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_sub, map_smul, map_one]
    rfl
  rw [h, ← map_pow]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

private def frobZ : k ≃ₐ[ℤ] k := AlgEquiv.ofRingEquiv (f := frobeniusEquiv k p) (fun n => by simp)

private def E : (k ⊗[ℤ] C) ≃ₐ[ℤ] (k ⊗[ℤ] C) := Algebra.TensorProduct.congr (frobZ (k := k) p) AlgEquiv.refl

private theorem E_tmul (l : k) (c : C) : E p (l ⊗ₜ[ℤ] c) = (l ^ p) ⊗ₜ[ℤ] c := by
  simp [E, frobZ, frobenius_def]

private theorem E_smul (l : k) (x : k ⊗[ℤ] C) : E p (l • x) = l ^ p • E p x := by
  induction x with
  | tmul a c => simp [TensorProduct.smul_tmul', E_tmul, mul_pow]
  | add x y hx hy => simp [smul_add, hx, hy]

private theorem E_mem (ν : C → k) (x : k ⊗[ℤ] C) : E p x ∈ W (fun c => ν c ^ p) ↔ x ∈ W ν := by
  rw [mem_W, mem_W]
  refine forall_congr' fun c => exists_congr fun n => ?_
  have h : E p (((1 : k) ⊗ₜ[ℤ] c - ν c ⊗ₜ[ℤ] (1 : C)) ^ n * x)
      = ((1 : k) ⊗ₜ[ℤ] c - (ν c ^ p) ⊗ₜ[ℤ] (1 : C)) ^ n * E p x := by
    rw [map_mul, map_pow, map_sub, E_tmul, E_tmul, one_pow]
  rw [← h]
  exact map_eq_zero_iff _ (E p).injective

private theorem finrank_W_pow (ν : C → k) :
    Module.finrank k ↥(W (fun c => ν c ^ p)) = Module.finrank k ↥(W ν) := by
  let j : ↥(W ν) ≃+ ↥(W (fun c => ν c ^ p)) :=
    { toFun := fun x => ⟨E p x.1, (E_mem p ν x.1).2 x.2⟩
      invFun := fun y => ⟨(E p).symm y.1, (E_mem p ν _).1 (by simpa using y.2)⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun y => Subtype.ext (by simp)
      map_add' := fun x y => Subtype.ext (by simp) }
  have hr := rank_eq_of_equiv_equiv (R := k) (R' := k) (M := ↥(W ν)) (M₁ := ↥(W (fun c => ν c ^ p)))
    (⟨fun l => l ^ p, by simp [(Fact.out : p.Prime).ne_zero]⟩ : ZeroHom k k) j
    (frobeniusEquiv k p).bijective (fun r m => Subtype.ext (E_smul p r m.1))
  exact (congrArg Cardinal.toNat hr).symm

end UpperTheory.Gal.Ord.DimsAlg

namespace UpperTheory.Gal.Ord.DimsCoh

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {k : Type} [Field k] {t : Sp k ⟶ Sp R}

private def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) :=
  RingHom.mk'
    { toFun := coh o
      map_one' := by
        haveI := o.act.hom
        refine LinearMap.ext fun x => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_id _ _ _ (by rw [map_one, o.act.one]) x
      map_mul' := fun x y => by
        haveI := o.act.hom
        refine LinearMap.ext fun c => ?_
        exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_comp _ _ _ _ _ (by rw [mul_comm x y, map_mul, o.act.mul]) c }
    fun x y => by
      haveI := o.act.hom
      refine LinearMap.ext fun c => ?_
      exact GlobalTheory.AbDatum.DRAct.primPull_of_eq_mul _ _ _ _ _ (by rw [map_add (f := _), o.act.add]) c

end UpperTheory.Gal.Ord.DimsCoh

open UpperTheory.Gal.Ord.DimsAlg UpperTheory.Gal.Ord.DimsCoh in
theorem UpperTheory.Gal.Ord.dims :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      ∀ j : ℕ, Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c) ^ p ^ j)) =
        Module.finrank k ↥(⨅ c, (coh o c).maxGenEigenspace (β (b.t i c))) := by
  intro p _ D R _ b N hN hNp _ k _ _ hk β o i w f _ _ _ π j
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
  obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
  haveI := hfd
  haveI : Module.Finite k (primDR o.A) := (Module.finite_dual_iff k).1 hfd
  haveI := D.freeLa
  haveI := D.finLa
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hk
  obtain ⟨l, hlp, hl⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : l.Coprime p := (Nat.coprime_primes hl (Fact.out : p.Prime)).2 (by omega)
  have hcopj : ∀ j : ℕ, (l ^ j).Coprime p := fun j => Nat.Coprime.pow_left j hcop
  have hposj : ∀ j : ℕ, 0 < l ^ j := fun j => pow_pos hl.pos j
  have hlk : (l : k) ≠ 0 := by
    have hu := (b.unit l hcop).map β
    rw [map_natCast] at hu
    exact hu.ne_zero
  obtain ⟨I, -⟩ := o.geom k (𝟙 _) β (by rw [Category.id_comp])
  have hc : ∀ c : 𝓞 D.F, LinearMap.charpoly (cohHom o c) =
      ((LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n)).map (Int.castRingHom k) := by
    intro c
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    have e := GlobalTheory.T.charpoly_deRhamHomology_endomorphism_eq_map_ladic k o.A o.ab (o.act.act (algebraMap (𝓞 D.F) D.O c)) D.La
      (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) l hl hlk (fun j => I.ev (l ^ j))
      (fun j x y => I.add (l ^ j) x y) (fun j x => I.lin (l ^ j) _ x)
      (fun j x => I.ker (l ^ j) (hposj j) (hcopj j) x) (fun j q => I.onto (l ^ j) (hposj j) (hcopj j) q)
    rw [GlobalTheory.T.charpoly_la_eq_pow p D c] at e
    rw [← e]
    exact (GlobalTheory.DeRhamCharpolyP.charpoly_dualMap _).symm
  have key := fun χ : 𝓞 D.F →+* k => GlobalTheory.T.finrank_jointWeightSpace_eq_of_charpoly k (𝓞 D.F) ↥(primDR o.A) (cohHom o) (D.m * D.n) hc χ
  have e1 := key ((iterateFrobenius k p j).comp (β.comp (b.t i)))
  have e2 := key (β.comp (b.t i))
  have hW : ∀ (j : ℕ) , Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c) ^ p ^ j)) =
      Module.finrank k ↥(W (C := 𝓞 D.F) (fun c => β (b.t i c))) := by
    intro j
    induction j with
    | zero => exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by simp)
    | succ j ih =>
      rw [← ih, ← finrank_W_pow p (fun c => β (b.t i c) ^ p ^ j)]
      exact congrArg (fun ν : 𝓞 D.F → k => Module.finrank k ↥(W ν)) (funext fun c => by rw [_root_.pow_succ, _root_.pow_mul])
  simp only [RingHom.comp_apply, iterateFrobenius_def] at e1 e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  exact congrArg (D.m * D.n * ·) (hW j)
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RadicalStalks.TmulPMul
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

private lemma tmul_p_mul (p : ℕ) (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (l : k) (t : C) :
    l ⊗ₜ[ℤ] ((p : C) * t) = 0 := by
  have h1 : (p : C) * t = p • t := (nsmul_eq_mul p t).symm
  have h2 : (p • l : k) = 0 := by rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [h1, ← TensorProduct.smul_tmul, h2, TensorProduct.zero_tmul]

private lemma core (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] :
    ∃ (I : Type) (β : I → k),
      (∀ x : k ⊗[ℤ] C, ∃ c : I →₀ C, x = c.sum fun j d => β j ⊗ₜ[ℤ] d) ∧
      (∀ (s : Finset I) (c : I → C), ∑ j ∈ s, β j ⊗ₜ[ℤ] c j = 0 → ∀ j ∈ s, (p : C) ∣ c j) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  let B := Module.Basis.ofVectorSpace (ZMod p) k
  let J : Ideal C := Ideal.span {(p : C)}
  have hpJ : (Int.castAddHom (C ⧸ J)) (p : ℤ) = 0 := by
    show ((p : ℤ) : C ⧸ J) = 0
    rw [Int.cast_natCast, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  let φ : ZMod p →+ C ⧸ J := ZMod.lift p ⟨Int.castAddHom (C ⧸ J), hpJ⟩
  have hφ1 : φ 1 = 1 := by
    have h1 := ZMod.lift_coe p ⟨Int.castAddHom (C ⧸ J), hpJ⟩ (1 : ℤ)
    simpa using h1
  refine ⟨_, B, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul l t =>
      refine ⟨(B.repr l).mapRange (fun r => ((r.val : ℕ) : C) * t) (by simp), ?_⟩
      rw [Finsupp.sum_mapRange_index (fun _ => TensorProduct.tmul_zero _ _)]
      have hl := B.linearCombination_repr l
      rw [Finsupp.linearCombination_apply] at hl
      conv_lhs => rw [← hl]
      rw [Finsupp.sum, Finsupp.sum, TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hs : (B.repr l j) • B j = (B.repr l j).val • B j := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (B.repr l j)]
        rw [Nat.cast_smul_eq_nsmul]
      rw [hs, TensorProduct.smul_tmul, nsmul_eq_mul]
    | add x y hx hy =>
      obtain ⟨c1, rfl⟩ := hx
      obtain ⟨c2, rfl⟩ := hy
      exact ⟨c1 + c2, by rw [Finsupp.sum_add_index' (fun _ => TensorProduct.tmul_zero _ _) (fun _ _ _ => TensorProduct.tmul_add _ _ _)]⟩
  · intro s c hs j hj
    let L : k →ₗ[ℤ] C →ₗ[ℤ] C ⧸ J := LinearMap.mk₂ ℤ (fun l t => φ (B.repr l j) * Ideal.Quotient.mk J t)
      (by intros; simp [add_mul])
      (by intro n m t; rw [map_zsmul, Finsupp.smul_apply, map_zsmul, smul_mul_assoc])
      (by intros; simp [mul_add])
      (by intro n m t; rw [map_zsmul, mul_smul_comm])
    have h0 := congrArg (TensorProduct.lift L) hs
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at h0
    have step : ∀ i ∈ s, TensorProduct.lift L (B i ⊗ₜ[ℤ] c i) = if i = j then Ideal.Quotient.mk J (c i) else 0 := by
      intro i _
      rw [TensorProduct.lift.tmul]
      by_cases h : i = j
      · subst h; simp [L, hφ1]
      · simp [L, h, Finsupp.single_apply]
    rw [Finset.sum_congr rfl step, Finset.sum_ite_eq' s j, if_pos hj, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact Ideal.mem_span_singleton.mp h0

private lemma exact1 {R : Type} [CommRing R] (g a b : R) (h : ∀ x : R, g * x = 0 → ∃ u v, x = a * u + b * v)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : g • x = 0) :
    ∃ u v : M, x = a • u + b • v := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, g * s x m = 0 := by
    intro m
    have h0 : s (g • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u v huv using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ∑ m ∈ (s x).support, v m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [huv m, add_smul, mul_smul, mul_smul]
  rfl

private lemma exact2 {R : Type} [CommRing R] (e g a : R) (h : ∀ x : R, a * x = 0 → ∃ u, e * x = g * u)
    {M : Type 1} [AddCommGroup M] [Module R M] [Module.Projective R M] (x : M) (hx : a • x = 0) :
    ∃ u : M, e • x = g • u := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Projective R M).out
  have hy : ∀ m, a * s x m = 0 := by
    intro m
    have h0 : s (a • x) = 0 := by rw [hx, map_zero]
    rw [map_smul] at h0
    have h1 := congrArg (fun y => y m) h0
    simpa using h1
  choose u hu using fun m => h _ (hy m)
  refine ⟨∑ m ∈ (s x).support, u m • m, ?_⟩
  have hx' := hs x
  rw [Finsupp.linearCombination_apply] at hx'
  conv_lhs => rw [← hx']
  rw [Finsupp.sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← mul_smul, hu m, mul_smul]
  rfl

theorem UpperTheory.Gal.Ord.proj :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] (C : Type) [CommRing C] (w : Ideal C) (f : ℕ) (π : Par p w f)
      (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] C) M] [Module.Projective (k ⊗[ℤ] C) M],
      (∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.g) • x = 0 → ∃ u v : M, x = ((1 : k) ⊗ₜ[ℤ] π.a) • u + ((1 : k) ⊗ₜ[ℤ] (1 - π.ε)) • v) ∧
      ∀ x : M, ((1 : k) ⊗ₜ[ℤ] π.a) • x = 0 → ∃ u : M, ((1 : k) ⊗ₜ[ℤ] π.ε) • x = ((1 : k) ⊗ₜ[ℤ] π.g) • u := by
  intro p _ k _ _ C _ w f π M _ _ _
  obtain ⟨I, β, hspan, hind⟩ := core p k C
  constructor
  · intro x hx
    refine exact1 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.g * c j := hind c.support (fun j => π.g * c j) hy
    choose! u v hd using fun j (hj : j ∈ c.support) => π.annG (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ∑ j ∈ c.support, β j ⊗ₜ[ℤ] v j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, ← TensorProduct.tmul_add]
    have hc : c j = π.a * u j + (1 - π.ε) * v j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
  · intro x hx
    refine exact2 _ _ _ ?_ x hx
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    rw [Finsupp.sum, Finset.mul_sum] at hy
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul] at hy
    have key : ∀ j ∈ c.support, (p : C) ∣ π.a * c j := hind c.support (fun j => π.a * c j) hy
    choose! u hd using fun j (hj : j ∈ c.support) => π.annA (c j) (key j hj)
    refine ⟨∑ j ∈ c.support, β j ⊗ₜ[ℤ] u j, ?_⟩
    rw [Finsupp.sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    obtain ⟨t, ht⟩ := hd j hj
    simp only [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
    have hc : π.ε * c j = π.g * u j + p * t := by rw [← ht]; ring
    rw [hc, TensorProduct.tmul_add, tmul_p_mul p k C, add_zero]
end

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES UpperTheory.Gal.Ord
open scoped TensorProduct

namespace UpperTheory.Gal.Ord.LinPf

variable {k : Type} [Field k]

private theorem dual_annG {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C)
    (h : ∀ x : Module.Dual k P, (ρ a).dualMap x = 0 → ∃ u, (ρ ε).dualMap x = (ρ g).dualMap u)
    (x : P) (hx : ρ g x = 0) : ∃ u v, x = ρ a u + ρ (1 - ε) v := by
  have hW : x ∈ LinearMap.range (ρ a) ⊔ LinearMap.range (ρ (1 - ε)) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ a).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_left ⟨y, rfl⟩)
    have h2 : (ρ (1 - ε)).dualMap φ = 0 :=
      LinearMap.ext fun y ↦ hφ _ (Submodule.mem_sup_right ⟨y, rfl⟩)
    obtain ⟨u, hu⟩ := h φ h1
    have h3 : φ = (ρ ε).dualMap φ + (ρ (1 - ε)).dualMap φ := by
      refine LinearMap.ext fun y ↦ ?_
      have e : ρ ε y + ρ (1 - ε) y = y := by
        rw [map_sub, map_one]; simp
      rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, ← map_add (f := _), e]
    rw [h3, h2, add_zero, hu, LinearMap.dualMap_apply, hx, map_zero]
  obtain ⟨y, ⟨u, rfl⟩, z, ⟨v, rfl⟩, e⟩ := Submodule.mem_sup.1 hW
  exact ⟨u, v, e.symm⟩

private theorem dual_annA {C P : Type*} [CommRing C] [AddCommGroup P] [Module k P]
    (ρ : C →+* Module.End k P) (a ε g : C) (hε : ρ ((1 - ε) * ε) = 0)
    (h : ∀ x : Module.Dual k P, (ρ g).dualMap x = 0 →
      ∃ u v, x = (ρ a).dualMap u + (ρ (1 - ε)).dualMap v)
    (x : P) (hx : ρ a x = 0) : ∃ u, ρ ε x = ρ g u := by
  have hW : ρ ε x ∈ LinearMap.range (ρ g) := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have h1 : (ρ g).dualMap φ = 0 := LinearMap.ext fun y ↦ hφ _ ⟨y, rfl⟩
    obtain ⟨u, v, rfl⟩ := h φ h1
    have e1 : ρ a (ρ ε x) = 0 := by
      have : ρ a * ρ ε = ρ ε * ρ a := by rw [← map_mul, ← map_mul, mul_comm]
      have := LinearMap.congr_fun this x
      simpa [hx] using this
    have e2 : ρ (1 - ε) (ρ ε x) = 0 := by
      have : ρ (1 - ε) * ρ ε = 0 := by rw [← map_mul, hε]
      exact LinearMap.congr_fun this x
    rw [LinearMap.add_apply, LinearMap.dualMap_apply, LinearMap.dualMap_apply, e1, e2, map_zero,
      map_zero, add_zero]
  obtain ⟨u, hu⟩ := hW
  exact ⟨u, hu.symm⟩

variable {p : ℕ} [Fact p.Prime]

private theorem frob_of_mem (hk : (p : k) = 0) (A : Over (Sp k)) [GrpObj A] (hA : IsAbelianScheme A)
    (c : primDR A) (hc : c ∈ PrimitiveSubmodule A) : frobDR p k hk A c = 0 := by
  letI : Algebra k k := (frobR p k hk).toAlgebra
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k A hA
  have hπ := isGrpPullback_pullback A (spMap (frobR p k hk))
  obtain ⟨F, hFm, hF⟩ := GlobalTheory.T.exists_relativeFrobenius_grpScheme_charP p k hk A _ _ hπ
  have hker := (GlobalTheory.T.range_relativeFrobenius_primitiveDeRham_eq_conjugate GlobalTheory.abelianDeRham.2.2.1 p k hk A _ _ hπ F hF g hA hg).2
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hπ
  have e : primPull (dp0 k) (𝟙 _) F (m.pull c) = frobDR p k hk A c :=
    GrpMor.pull_pull m (homMor (dp0 k) (𝟙 _) F) (frobMor p k hk A (cast_left p k hk A))
      (fun _ ↦ rfl) hF c
  rw [← e]
  exact hker (m.isMor.pullback1_mem_hodgeFiltration hc)

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {t : Sp k ⟶ Sp R}

private theorem hom_apply (o : Obj b N t) (c : 𝓞 D.F) (h : HdR o.A) (x : primDR o.A) :
    hom o c h x = h (coh o c x) := rfl

private theorem sep (o : Obj b N t) {x y : primDR o.A} (e : ∀ h : HdR o.A, h x = h y) : x = y := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
  intro h
  have := e h
  rw [map_sub, sub_eq_zero]
  exact this

private theorem hom_add (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x + y) = hom o x + hom o y := by
  simp only [hom, map_add (f := _)]

private theorem hom_mul (o : Obj b N t) (x y : 𝓞 D.F) : hom o (x * y) = hom o x * hom o y := by
  simp only [hom, map_mul]

private theorem hom_one (o : Obj b N t) : hom o 1 = 1 := by
  simp only [hom, map_one]

private noncomputable def cohHom (o : Obj b N t) : 𝓞 D.F →+* Module.End k (primDR o.A) where
  toFun := coh o
  map_one' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_one]; rfl
  map_mul' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [mul_comm x y, ← hom_apply, hom_mul]; rfl
  map_zero' := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply]; simp [hom]
  map_add' x y := LinearMap.ext fun v ↦ sep o fun h ↦ by
    rw [← hom_apply, hom_add, LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, map_add (f := _)]; rfl

private theorem cohHom_natCast_zero (hk : (p : k) = 0) (o : Obj b N t) : cohHom o (p : 𝓞 D.F) = 0 := by
  rw [map_natCast, ← map_natCast (algebraMap k (Module.End k (primDR o.A))) p, hk, map_zero]

end UpperTheory.Gal.Ord.LinPf

open UpperTheory.Gal.Ord.LinPf in
theorem UpperTheory.Gal.Ord.lin :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 →
      ∀ (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (β : R →+* k) (o : Obj b N (spMap β)) (i : Fin D.a) (w : Ideal (𝓞 D.F)) (f : ℕ),
      RingHom.ker (β.comp (b.t i)) = w → Ideal.absNorm w = p ^ f → 0 < f → ∀ π : Par p w f,
      Lin p π (β.comp (b.t i)) (coh o) (PrimitiveSubmodule o.A) (frobDR p k hk o.A).toAddMonoidHom := by
  intro p _ D R _ b N hN hNp hm k _ _ hk β o i w f hw hn hf π
  obtain ⟨h1, ⟨h₀, h2, h3⟩, -⟩ := UpperTheory.Gal.Ord.lie p D R b N hN hNp hm k hk β o i w f hw hn hf π
  haveI : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hk
  letI := tensorModule (dp0 k) (𝟙 _) (o.act.toF D)
  have hP := GlobalTheory.CrysProj.hdR_projective D.F k o.A o.ab (o.act.toF D)
  obtain ⟨hG, hA⟩ := UpperTheory.Gal.Ord.proj p k (𝓞 D.F) w f π (HdR o.A)
  have hs : ∀ (c : 𝓞 D.F) (x : HdR o.A), ((1 : k) ⊗ₜ[ℤ] c) • x = (cohHom o c).dualMap x := fun c x ↦ by
    change actAlg (dp0 k) (𝟙 _) (o.act.toF D) ((1 : k) ⊗ₜ[ℤ] c) x = _
    rw [actAlg_tmul, one_smul]
    rfl
  have hε : cohHom o ((1 - π.ε) * π.ε) = 0 := by
    obtain ⟨u, hu⟩ := π.idem
    have e : (1 - π.ε) * π.ε = (p : 𝓞 D.F) * (-u) := by
      linear_combination -hu
    rw [e, map_mul, cohHom_natCast_zero hk, zero_mul]
  refine
    { fin := ?_
      add := fun x y ↦ (cohHom o).map_add x y
      mul := fun x y ↦ (cohHom o).map_mul x y
      one := (cohHom o).map_one
      ker := hw
      semi := fun l x ↦ ?_
      comm := fun c x ↦ ?_
      kerΦ := fun x ↦ ⟨fun h ↦ GlobalTheory.T.frobenius_kernel_primitive_de_rham_hodge p k hk o.A o.ab x h, fun h ↦ frob_of_mem hk o.A o.ab x h⟩
      stab := fun c x hx ↦ ?_
      eig := fun c x hx ↦ ?_
      line := ?_
      annG := fun x hx ↦ ?_
      annA := fun x hx ↦ ?_
      dims := UpperTheory.Gal.Ord.dims p D R b N hN hNp hm k hk β o i w f hw hn hf π }
  · obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o.A o.ab
    have H := GlobalTheory.abelianDeRham
    obtain ⟨hfd, -, -⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o.A g o.ab hg
    exact Module.finite_dual_iff k |>.1 hfd
  · change frobDR p k hk o.A (l • x) = l ^ p • frobDR p k hk o.A x
    rw [LinearMap.map_smulₛₗ, frobR_apply]
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact GlobalTheory.AbDatum.frobDR_primPull p hk _ x
  · haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
    exact (homMor (dp0 k) (𝟙 _) (o.act.act (algebraMap (𝓞 D.F) D.O c))).isMor.pullback1_mem_hodgeFiltration hx
  · refine sep o fun h ↦ ?_
    have e := (Submodule.mem_dualAnnihilator _).1 (h1 c h) x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at e
    have ec : coh o c (coh o π.ε x) = coh o π.ε (coh o c x) := by
      have := LinearMap.congr_fun ((cohHom o).map_mul c π.ε) x
      rw [mul_comm, (cohHom o).map_mul] at this
      exact this.symm
    rw [ec, map_smul, e]
    rfl
  · have hx₀ : ∃ x ∈ PrimitiveSubmodule o.A, hom o π.ε h₀ x ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h2 ((Submodule.mem_dualAnnihilator _).2 hc)
    obtain ⟨x, hx, hne⟩ := hx₀
    rw [hom_apply] at hne
    refine ⟨x, hx, fun e ↦ hne (by rw [e, map_zero]), fun y hy ↦ ?_⟩
    refine ⟨h₀ (coh o π.ε y) / h₀ (coh o π.ε x), sep o fun h ↦ ?_⟩
    obtain ⟨m, hm⟩ := h3 h
    have ey := (Submodule.mem_dualAnnihilator _).1 hm y hy
    have ex := (Submodule.mem_dualAnnihilator _).1 hm x hx
    rw [LinearMap.sub_apply, LinearMap.smul_apply, hom_apply, hom_apply, smul_eq_mul,
      sub_eq_zero] at ey ex
    rw [map_smul, ey, ex, smul_eq_mul]
    field_simp
  · refine dual_annG (cohHom o) π.a π.ε π.g (fun y hy ↦ ?_) x hx
    obtain ⟨u, hu⟩ := hA y (by rw [hs]; exact hy)
    exact ⟨u, by rw [← hs, ← hs]; exact hu⟩
  · refine dual_annA (cohHom o) π.a π.ε π.g hε (fun y hy ↦ ?_) x hx
    obtain ⟨u, v, huv⟩ := hG y (by rw [hs]; exact hy)
    exact ⟨u, v, by rw [← hs, ← hs]; exact huv⟩
