module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

section Transport

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {B : LocBase0 H what₂} {i : LocT B} {j : ℕ} {w : what₂.places.Pl}
  (h : jOf B i = j ∧ wOf B i = w)

def trO : OOf B i ≃+* B.Oc j w := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

def trK : FractionRing (OOf B i) ≃+* FractionRing (B.Oc j w) := by obtain ⟨rfl, rfl⟩ := h; exact RingEquiv.refl _

theorem trK_alg (z : OOf B i) : trK h (algebraMap _ _ z) = algebraMap _ _ (trO h z) := by obtain ⟨rfl, rfl⟩ := h; rfl

theorem trK_ec (x : what₂.LL) : trK h (B.ec _ _ x) = B.ec j w x := by obtain ⟨rfl, rfl⟩ := h; rfl

variable (hC : PartCompl B) (hL : MtLoc B hC)

def trPsi : TensorProduct (OOf B i) (FractionRing (OOf B i)) (MtSub B hC i) →ₛₗ[(trK h).toRingHom] B.V j w := by
  obtain ⟨rfl, rfl⟩ := h
  exact { toFun := PsiC B hC hL i, map_add' := map_add _, map_smul' := fun c z => map_smul (PsiC B hC hL i) c z }

theorem trPsi_inj : Function.Injective (trPsi h hC hL) := by obtain ⟨rfl, rfl⟩ := h; exact PsiC_inj B hC hL i

theorem trPsi_range (y : B.V j w) : y ∈ NCov.part (heckeAlg0 B j w) (mxC B j w i) ↔ ∃ z, trPsi h hC hL z = y := by
  obtain ⟨rfl, rfl⟩ := h
  rw [mxC_self]
  exact PsiC_range B hC hL i y

theorem trPsi_pr (x : what₂.MtL (what₂.muTw (wOf B i)) (jOf B i)) (x' : what₂.MtL (what₂.muTw w) j) (hx : HEq x' x) :
    trPsi h hC hL (prMtC B hC hL i x) - B.iV j w x' ∈ NCov.off (heckeAlg0 B j w) (mxC B j w i) := by
  obtain ⟨rfl, rfl⟩ := h
  obtain rfl := eq_of_heq hx
  rw [mxC_self]
  exact PsiC_pr B hC hL i _

def trX : XOf B i ≃ {ψ : heckeAlg0 B j w →ₐ[B.Oc j w] B.Oc j w //
    NCov.cls ψ = mxC B j w i ∧ NCov.W (heckeAlg0 B j w) (NCov.pt ψ) ≠ ⊥} := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun x => ⟨x.1, x.2.1.trans (mxC_self B i).symm, x.2.2⟩, fun x => ⟨x.1, x.2.1.trans (mxC_self B i), x.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

theorem trX_hT (x : XOf B i) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) :
    trO h ((hTOf B i v k : XOf B i → OOf B i) x) = (trX h x).1 ⟨B.hK j w v k, Algebra.subset_adjoin ⟨v, k, hvk, rfl⟩⟩ := by
  obtain ⟨rfl, rfl⟩ := h
  exact ptX_val B i v k hvk x

theorem trPsi_act (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd))
    (hA : ActHK B hs hd hL hAct) (v : PlE H) (k : ℕ) (hvk : GenAt0 H (what₂.places.resChar w) (B.Qw w) v k) (z) :
    trPsi h _ hL (((actC B (partCompl_of hs hd) hAct i) (hTOf B i v k)).baseChange (FractionRing (OOf B i)) z) =
      B.hK j w v k (trPsi h _ hL z) := by
  obtain ⟨rfl, rfl⟩ := h
  exact hA i v k hvk z

include h in
theorem tr_max : (mxC B j w i).IsMaximal := by obtain ⟨rfl, rfl⟩ := h; exact mxC_max B i

end Transport

variable {D : D7}

def recBase (M : MtFam D) (B0 : LocBase0 D.host D.what₂)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w) : NLocBase D M where
  Oc := B0.Oc
  ec := B0.ec
  ec_w := B0.ec_w
  V := B0.V
  iV := B0.iV
  iV_basis := B0.iV_basis
  Qc _ w := B0.Qw w
  hL := B0.hL
  hL_def := hdef
  hK := B0.hK
  hK_def := B0.hK_def
  split := B0.split
  Qc_over _ := hO
  Qc_conj _ := hc

section Spec

variable (B0 : LocBase0 D.host D.what₂) (C : NChoice D) (hs : HeckeStd0 B0) (hd : FinDimV B0)
  (hL : MtLoc B0 (partCompl_of hs hd))
  (hMF : ∀ i, Module.Free (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hMFin : ∀ i, Module.Finite (OOf B0 i) (MtSub B0 (partCompl_of hs hd) i))
  (hTL : ∀ i, IsLocalRing (TOf B0 i)) (hAct : ActEx B0 (partCompl_of hs hd))
  (hEig : ∀ i x, heckeEig (TOf B0 i) (actC B0 (partCompl_of hs hd) hAct i) x ≠ ⊥)
  (tw : ∀ i : LocT B0, D.ntw.O0 (C.twI (wOf B0 i)) →+* OOf B0 i)
  (ps : ∀ i : LocT B0, G D.host.E D.nd.Om →* (OOf B0 i)ˣ)
  (hChi : ∀ i c, Continuous (fun g => ((chiN B0 C tw ps i c g : (OOf B0 i)ˣ) : OOf B0 i)))
  (hSQs : ∀ i v, v ∈ (exceptional_places_finite D.host (lOf B0 i)).toFinset ∨ v ∈ B0.Qw (wOf B0 i) → IsSplitPl D.host v)
  (hSQd : ∀ i, Disjoint (exceptional_places_finite D.host (lOf B0 i)).toFinset (B0.Qw (wOf B0 i)))
  (hQl : ∀ w v, v ∈ B0.Qw w → v ∉ placesOver D.host.E (D.what₂.places.resChar w))
  (hRam : ∀ i, ∀ v ∈ B0.Qw (wOf B0 i), ∃ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chi1N B0 C tw ps i g ≠ 1)
  (hI : OsInt B0) (hBF : ∀ i, Module.Free (OOf B0 i) (BjC B0 hI i))

attribute [local instance] LocBase0.algOc


set_option maxHeartbeats 1000000 in
theorem nonempty_spec
    (hTwE : ∀ (a : LocT B0) (x : D.LL0) (y : D.ntw.O0 (C.twI (wOf B0 a))),
      algebraMap (D.ntw.O0 (C.twI (wOf B0 a))) (FractionRing (D.ntw.O0 (C.twI (wOf B0 a)))) y =
        (if C.sd (wOf B0 a) then D.ntw.emb0 (C.twI (wOf B0 a)) else D.ntw.emb0b (C.twI (wOf B0 a))) x →
      B0.ec (jOf B0 a) (wOf B0 a) (x : D.what₂.LL) = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y))
    (hOrd : ∀ a g, ∃ n : ℕ, ps a g ^ (lOf B0 a ^ n) = 1)
    (hOpen : ∀ a, IsOpen ((ps a).ker : Set (G D.host.E D.nd.Om)))
    (hAnti : ∀ a, AntiHom D.ntw.cc (ps a))
    (hRamP : ∀ a, RamExactly (ps a) (↑(B0.Qw (wOf B0 a)) : Set (HeightOneSpectrum (𝓞 D.host.E))))
    (hPl : ∀ a v, v ∈ placesOver D.host.E (lOf B0 a) → ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v →
      ∀ σ ∈ Dec (F := D.host.E) A, ps a σ = 1)
    (pl : PlSide D) (M : MtFam D) (big : D.what₂.places.Pl → Finset ℂ)
    (hdef : ∀ j w (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
      (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)),
      GenAt D (D.what₂.places.resChar w) (B0.Qw w) v k → IsConjPl D.host v s.w → IsUnif D.host.E s.v ϖ →
      ∀ x, (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j (B0.hL j w v k x)) =
        NG.tN (M (D.what₂.muTw w) j h1 h2).J s ϖ k ((M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x)))
    (hO : ∀ w (v v' : PlE D.host), v ∈ B0.Qw w →
      (∃ v₀ : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)), NG.OverPl v v₀ ∧ NG.OverPl v' v₀) → v' ∈ B0.Qw w)
    (hc : ∀ w (v v' : PlE D.host), v' ∈ B0.Qw w → IsConjPl D.host v v' → v ∈ B0.Qw w)
    (hQ : ∀ w, B0.Qw w = C.Q w)
    (iq : ∀ j w, FractionRing (B0.Oc j w) →+* Qbar (D.what₂.places.resChar w))
    (hiA : ∀ j w (z : ℤ_[D.what₂.places.resChar w]), iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))
      (algebraMap ℤ_[D.what₂.places.resChar w] (B0.Oc j w) z)) =
        algebraMap ℚ_[D.what₂.places.resChar w] (Qbar (D.what₂.places.resChar w)) (z : ℚ_[D.what₂.places.resChar w]))
    (hiL : ∀ j w x, pl.ι w (iq j w (B0.ec j w x)) = D.what₂.embLL x)
    (hBig : ∀ j w, ∀ z ∈ big w, ∃ x, pl.ι w (iq j w x) = z)
    (hAHK : ActHK B0 hs hd hL hAct) (hD : PlGwDisj D)
    (hψ : ∀ (a : LocT B0) (g : G D.host.E D.nd.Om) (y : D.what₂.LL), C.embW (wOf B0 a) y =
      algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
        (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
          ((C.psi' (wOf B0 a) (D.ntw.art (C.twI (wOf B0 a)) (C.Q (wOf B0 a)) g) :
            (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))ˣ) : D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a)))) →
      B0.ec _ _ y = algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) ((ps a g : (OOf B0 a)ˣ) : OOf B0 a))
    (hTwA : ∀ a : LocT B0, haveI : Fact (D.ntw.l (C.twI (wOf B0 a))).Prime := D.ntw.lPrime (C.twI (wOf B0 a))
      ∀ (z : ℤ_[D.ntw.l (C.twI (wOf B0 a))]) (z' : ℤ_[D.what₂.places.resChar (wOf B0 a)]), HEq z z' →
      tw a (@algebraMap _ (D.ntw.O0 (C.twI (wOf B0 a))) _ _ (D.ntw.algO0 (C.twI (wOf B0 a))) z) = algebraMap _ (OOf B0 a) z')
    (hTwR : ∀ a : LocT B0, ∃ (Ω : Type) (_ : Field Ω) (τ : FractionRing (OOf B0 a) →+* Ω)
      (ι : FractionRing (C.Oe (wOf B0 a)) →+* Ω),
      (∀ y, τ (algebraMap (OOf B0 a) (FractionRing (OOf B0 a)) (tw a y)) =
        ι (algebraMap (C.Oe (wOf B0 a)) (FractionRing (C.Oe (wOf B0 a)))
          (algebraMap (D.ntw.Ok (C.twI (wOf B0 a)) (C.k' (wOf B0 a))) (C.Oe (wOf B0 a))
            (BlochKatoReduction.Gen.phiK D.ntw (C.twI (wOf B0 a)) (C.k' (wOf B0 a)) y)))) ∧
      ∀ x : D.what₂.LL, τ (B0.ec _ _ x) = ι (C.embW (wOf B0 a) x))
    (hBr : ∀ j w (u : PlE D.host), u ∈ placesOver D.host.E (D.what₂.places.resChar w) →
      ∃ Bw : LocBridge (D.what₂.places.resChar w) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 u)) (B0.Oc j w),
        (∀ x, x ∈ D.nd.plOm.1 u ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef D.host.condN Bw.LL ∧
        ∀ z : B0.Oc j w, iq j w (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w)) z) =
          ((Bw.toLL z : ↥Bw.LL.1) : Loc.Om (D.what₂.places.resChar w))) :
    Nonempty (NdSpec pl M C big (mkX B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF) (mkT B0 C hs hd hL hMF hMFin hTL hAct hEig tw ps hChi hSQs hSQd hQl hRam hI hBF hTwE hOrd hOpen hAnti hRamP hPl)) := ⟨{
  iq i := iq (jOf B0 i) (wOf B0 i)
  iq_alg i := hiA _ _
  iq_LL i := hiL _ _
  iq_big i := hBig _ _
  B := recBase M B0 hdef hO hc
  Q_eq j w i h := congrArg B0.Qw ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h).2
  mx := mxC B0
  mx_max j w i h := tr_max ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  mx_inj := mxC_inj B0 (locsFin_of hs hd)
  mx_all := mxC_all B0 (locsFin_of hs hd)
  phO j w i h := trO ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK j w i h := trK ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_alg j w i h := trK_alg ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  phK_emb j w i h := trK_ec ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  Psi j w i h := trPsi ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_inj j w i h := trPsi_inj ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_range j w i h := trPsi_range ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL
  Psi_pr j w i h x := trPsi_pr ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) (partCompl_of hs hd) hL x _ (cast_heq _ _)
  ptX j w i h := trX ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  ptX_hT j w i h := trX_hT ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
  iotaC j w := (pl.ι w).toRingHom.comp ((iq j w).comp (algebraMap (B0.Oc j w) (FractionRing (B0.Oc j w))))
  iotaC_coh j w i h z := by
    obtain ⟨rfl, rfl⟩ := ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h)
    rfl
  Qc_eq _ := hQ
  std := hs
  act_hK j w i h := trPsi_act ((locsC_mem B0 (locsFin_of hs hd) j w i).1 h) hs hd hL hAct hAHK
  twOf_eq _ := rfl
  twSide_eq _ := rfl
  psi_eq := hψ
  twO_alg := hTwA
  tw_reads a := ⟨tw a, HEq.rfl, hTwR a⟩
  heckeLoc_gamma_places _ := gamN_tg D hD
  nbr i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose
  nbr_ind i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.1
  self_good i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.1
  nbr_iq i w hw := (hBr (jOf B0 i) (wOf B0 i) w hw).choose_spec.2.2
  bj := bjC B0 hI
  bj_span := bjC_span B0 hI
  bj_rel i s hs' c := by
    obtain rfl : s = sOfC B0 hI i := RingHom.ext fun y => IsFractionRing.injective (OOf B0 i) (FractionRing (OOf B0 i))
      ((hs' y).trans (congrArg Subtype.val ((fracRangeEquiv (OOf B0 i)).apply_symm_apply ⟨_, hI _ _ y⟩)).symm)
    exact bjC_rel B0 hI i c }⟩

end Spec

end GlobalTheory.HeckeLocN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorsOnLocalisationSpaceSemisimple
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorsOnLocalisationSpaceSemisimple
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

section Lin

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem aeval_baseChange_map (L : Type) [Field L] [Algebra K L] (f : Module.End K V) (p : K[X]) :
    aeval (f.baseChange L) (p.map (algebraMap K L)) = (aeval f p).baseChange L := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add (f := _), map_add (f := _), hp, hr, map_add (f := _), LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem isSemisimple_baseChange [CharZero K] [FiniteDimensional K V] (f : Module.End K V)
    (hsq : Squarefree (minpoly K f)) (L : Type) [Field L] [Algebra K L] :
    Module.End.IsSemisimple (f.baseChange L) := by
  have hsep : (minpoly K f).Separable := PerfectField.separable_iff_squarefree.2 hsq
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (hsep.map (f := algebraMap K L)).squarefree
  rw [aeval_baseChange_map, minpoly.aeval, LinearMap.baseChange_zero]

variable {U : Type} [AddCommGroup U] [Module ℂ U] {σ : K →+* ℂ} (φ : V →ₛₗ[σ] U) (T : Module.End K V)
  (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
include h

theorem map_pow_apply (n : ℕ) (x : V) : φ ((T ^ n) x) = (S ^ n) (φ x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Module.End.mul_apply, h, ih, pow_succ', Module.End.mul_apply]

theorem map_aeval_apply (p : K[X]) (x : V) : φ (aeval T p x) = aeval S (p.map σ) (φ x) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply, map_add (f := _), hp, hq, Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply]
  | monomial n c =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply, Module.End.mul_apply,
      Module.algebraMap_end_apply, Module.algebraMap_end_apply, LinearMap.map_smulₛₗ, map_pow_apply φ T S h]

end Lin

end GlobalTheory.HeckeSemis

noncomputable section

namespace GlobalTheory.HeckeSemis

open Module

variable {U : Type} [AddCommGroup U] [Module ℂ U]

theorem isSemisimple_of_sq [FiniteDimensional ℂ U] (S : Module.End ℂ U)
    (h : ∀ (μ : ℂ) (u : U), S (S u - μ • u) = μ • (S u - μ • u) → S u = μ • u) : S.IsSemisimple := by
  apply GlobalTheory.WeilDeligne.isSemisimple_of_iSup_eigenspace
  rw [eq_top_iff, ← Module.End.iSup_maxGenEigenspace_eq_top S]
  refine iSup_mono fun μ => ?_
  intro u hu
  have hA : ∀ v, (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) v) = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro v hv
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hv ⊢
    rw [sub_eq_zero] at hv ⊢
    exact h μ v hv
  have step : ∀ k v, ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v = 0 → (S - μ • 1 : Module.End ℂ U) v = 0 := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      apply ih
      have e1 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1 + 1)) v =
          (S - μ • 1 : Module.End ℂ U) ((S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v)) := by
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      have e2 : ((S - μ • 1 : Module.End ℂ U) ^ (k + 1)) v =
          (S - μ • 1 : Module.End ℂ U) (((S - μ • 1 : Module.End ℂ U) ^ k) v) := by
        rw [pow_succ', Module.End.mul_apply]
      rw [e2]
      exact hA _ (e1 ▸ hv)
  rw [Module.End.mem_maxGenEigenspace] at hu
  obtain ⟨k, hk⟩ := hu
  rw [Module.End.mem_eigenspace_iff]
  have hz : (S - μ • 1 : Module.End ℂ U) u = 0 := by
    cases k with
    | zero => simp at hk; simp [hk]
    | succ k => exact step k u hk
  simpa [sub_eq_zero] using hz

theorem apply_eq_zero_of_sq [FiniteDimensional ℂ U] {A : Module.End ℂ U} (hA : A.IsSemisimple) {u : U}
    (hu : A (A u) = 0) : A u = 0 := by
  have h1 : u ∈ A.maxGenEigenspace 0 := by
    rw [Module.End.mem_maxGenEigenspace]
    exact ⟨2, by simpa [pow_two] using hu⟩
  rw [hA.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace, Module.End.mem_eigenspace_iff] at h1
  simpa using h1

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {σ : K →+* ℂ}

theorem squarefree_minpoly [FiniteDimensional K V] [FiniteDimensional ℂ U] (φ : V →ₛₗ[σ] U)
    (hφ : Function.Injective φ) (T : Module.End K V) (S : Module.End ℂ U) (h : ∀ x, φ (T x) = S (φ x))
    (hS : S.IsSemisimple) : Squarefree (minpoly K T) := by
  intro p hp
  obtain ⟨r, hr⟩ := hp
  have key : aeval T (p * r) = 0 := by
    ext x
    have hm : aeval T (minpoly K T) = 0 := minpoly.aeval K T
    rw [hr] at hm
    have h0 : aeval T p (aeval T p (aeval T r x)) = 0 := by
      have := LinearMap.congr_fun hm x
      simpa [map_mul, Module.End.mul_apply] using this
    have h1 : aeval S (p.map σ) (aeval S (p.map σ) (φ (aeval T r x))) = 0 := by
      rw [← map_aeval_apply φ T S h, ← map_aeval_apply φ T S h, h0, map_zero]
    have h2 := apply_eq_zero_of_sq (hS.aeval (p.map σ)) h1
    rw [← map_aeval_apply φ T S h] at h2
    have h3 : aeval T p (aeval T r x) = 0 := hφ (by rw [h2, map_zero])
    simpa [map_mul, Module.End.mul_apply] using h3
  have hdvd := minpoly.dvd K T key
  have hm0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
  rw [hr] at hdvd hm0
  have hne : p * r ≠ 0 := fun h => hm0 (by rw [mul_assoc, h, mul_zero])
  have h3 : p * (p * r) ∣ 1 * (p * r) := by rw [one_mul, ← mul_assoc]; exact hdvd
  exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hne).1 h3)

end GlobalTheory.HeckeSemis

namespace GlobalTheory.HeckeLocN

open Module

theorem finiteDimensional_MtL (D : D7) (μ : D.what₂.Tup) (j : ℕ) : FiniteDimensional D.what₂.LL (D.what₂.MtL μ j) := by
  have hli := (D.what₂.jMt_basis μ j (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))).1
  haveI := hli.finite
  exact Module.Finite.of_basis (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j))

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  set b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  haveI := hli.finite
  haveI := Fintype.ofFinite (Module.Free.ChooseBasisIndex D.what₂.LL (D.what₂.MtL μ j))
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro x hx
  have e : D.what₂.jMt μ j x = ∑ i, D.what₂.embLL (b.repr x i) • D.what₂.jMt μ j (b i) := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp [LinearMap.map_smulₛₗ]
  rw [e] at hx
  have hc := Fintype.linearIndependent_iff.1 hli _ hx
  apply b.repr.injective
  ext i
  simpa using hc i

theorem semisimpleTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → (∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f) → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → SemisimpleTw (base M C hR X hS) := by
  intro D M C hR X hS hStd hJord hGen hSpl
  intro j w h1 h2 _ v k hg
  obtain ⟨B, hBO, hBv⟩ := hGen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hSpl v hg.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hst := hStd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hjo := hJord D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hBO s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  set Mr := M (D.what₂.muTw w) j h1 h2 with hMr
  have t0 : NG.tN Mr.J s ϖ k (0 : GAf D.host.E D.R.nV → Mr.wt.W) = 0 := by
    have e := hst.2.1 0 (zero_mem _) 0 (zero_mem _) 1
    simp only [one_smul, add_zero] at e
    exact left_eq_add.mp e
  let S : Module.End ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) :=
    { toFun := fun f => ⟨NG.tN Mr.J s ϖ k f, hst.1 f f.2⟩
      map_add' := fun f g => Subtype.ext (by simpa using hst.2.1 f f.2 g g.2 1)
      map_smul' := fun c f => Subtype.ext (by
        have e := hst.2.1 f f.2 0 (zero_mem _) c
        simpa [t0] using e) }
  haveI : FiniteDimensional ℂ (NG.TypeSp Mr.wt.ρ Mr.J Mr.χ) := by
    rw [← Mr.real_range]; infer_instance
  haveI := finiteDimensional_MtL D (D.what₂.muTw w) j
  have hmem : ∀ x, Mr.real (D.what₂.jMt (D.what₂.muTw w) j x) ∈ NG.TypeSp Mr.wt.ρ Mr.J Mr.χ := fun x => by
    rw [← Mr.real_range]; exact LinearMap.mem_range_self _ _
  let φ : D.what₂.MtL (D.what₂.muTw w) j →ₛₗ[D.what₂.embLL] NG.TypeSp Mr.wt.ρ Mr.J Mr.χ :=
    { toFun := fun x => ⟨Mr.real (D.what₂.jMt _ j x), hmem x⟩
      map_add' := fun x y => Subtype.ext (by simp)
      map_smul' := fun c x => Subtype.ext (by simp [LinearMap.map_smulₛₗ]) }
  have hφ : Function.Injective φ := fun x y hxy =>
    jMt_injective D _ j (Mr.real_inj (congrArg Subtype.val hxy))
  have hcomm : ∀ x, φ (hLC (mt0 M) C.Q hR j w v k x) = S (φ x) := fun x =>
    Subtype.ext (hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu x)
  have hSs : S.IsSemisimple := GlobalTheory.HeckeSemis.isSemisimple_of_sq S (fun μ u hμ => Subtype.ext (by
    have e : NG.tN Mr.J s ϖ k (↑(S u - μ • u)) = μ • (↑(S u - μ • u) : GAf D.host.E D.R.nV → Mr.wt.W) :=
      congrArg Subtype.val hμ
    rw [Submodule.coe_sub, Submodule.coe_smul] at e
    exact hjo u u.2 μ e))
  have hsq := GlobalTheory.HeckeSemis.squarefree_minpoly φ hφ (hLC (mt0 M) C.Q hR j w v k) S hcomm hSs
  haveI : CharZero D.what₂.LL := RingHom.charZero D.what₂.embLL
  exact GlobalTheory.HeckeSemis.isSemisimple_baseChange _ hsq (FractionRing (OcC X j w))
end GlobalTheory.HeckeLocN
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorsOnLocalisationSpaceSemisimpleStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperators_on_localisation_space_semisimple : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X), HeckeStdPlain → (∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))), (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) → NG.HypOutside J χ B → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), s.v ∉ B → IsUnif L s.v ϖ → 1 ≤ k → k ≤ n → ∀ f ∈ NG.TypeSp a.ρ J χ, ∀ μ : ℂ, NG.tN J s ϖ k (NG.tN J s ϖ k f - μ • f) = μ • (NG.tN J s ϖ k f - μ • f) → NG.tN J s ϖ k f = μ • f) → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → SemisimpleTw (base M C hR X hS) := by
  first | exact @GlobalTheory.HeckeLocN.semisimpleTw_base | exact GlobalTheory.HeckeLocN.semisimpleTw_base | (intros; apply GlobalTheory.HeckeLocN.semisimpleTw_base <;> assumption)
end
end
