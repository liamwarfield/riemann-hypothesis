module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMap
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMap
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem stratHom_map_mulVec {m n : Type} [Fintype n] {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A')
    (M : Matrix m n A) (v : n → A) : (fun i => φ ((M.mulVec v) i)) = (M.map φ).mulVec (fun i => φ (v i)) := by
  funext i
  exact RingHom.map_mulVec φ M v i

theorem stratHom_coord_nat {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    (Y : Matrix (Fin d') (Fin d) bk.S) {B : Obj l ↥(OL K)} {N : Type} [AddCommGroup N] [Module B.A N]
    (V : Eval S B N) {Q Q' : Obj l ↥(OL K)} (r : Hom Q Q') (a : Hom B Q) (g : Hom bk.prism Q) (x : N) :
    (fun i => r.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) i)) =
      (Y.map (BK.hf (r.comp g))).mulVec (V.v (r.comp a) (r.comp g) x) := by
  rw [stratHom_map_mulVec]
  have e1 : (Y.map (BK.hf g)).map r.f = Y.map (BK.hf (r.comp g)) := by
    rw [Matrix.map_map]; rfl
  have e2 : (fun i => r.f (V.v a g x i)) = V.v (r.comp a) (r.comp g) x := by
    funext i; exact (V.v_nat r a g x i).symm
  rw [e1, e2]

theorem stratHom_coord_ε {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} {S : Strat bk d}
    {S' : Strat bk d'} {Y : Matrix (Fin d') (Fin d) bk.S} (hY : IsStratHom S S' Y) {B : Obj l ↥(OL K)} {N : Type}
    [AddCommGroup N] [Module B.A N] (V : Eval S B N) {Q : Obj l ↥(OL K)} (a : Hom B Q) (g g' : Hom bk.prism Q)
    (x : N) :
    (Y.map (BK.hf g)).mulVec (V.v a g x) = (S'.ε g g').mulVec ((Y.map (BK.hf g')).mulVec (V.v a g' x)) := by
  rw [V.v_ε a g g' x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hY.ε]

theorem evalHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N]
    [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'),
    ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  intro l _ K bk d d' S S' Y hY B N _ _ N' _ _ V V'
  obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B
  obtain ⟨inj, ev⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C N' V' h f hc
  have hz : ∀ x, ∀ (Q : Obj l ↥(OL K)) (p q : Hom C Q), p.comp h = q.comp h →
      (fun i => p.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i)) = (S'.ε (p.comp f) (q.comp f)).mulVec
        fun i => q.f (((Y.map (BK.hf f)).mulVec (V.v h f x)) i) := by
    intro x Q p q hpq
    have e : V.v (p.comp h) (p.comp f) x = V.v (q.comp h) (p.comp f) x := by rw [hpq]
    refine (stratHom_coord_nat Y V p h f x).trans ?_
    refine Eq.trans ?_ (congrArg (S'.ε (p.comp f) (q.comp f)).mulVec (stratHom_coord_nat Y V q h f x)).symm
    rw [e]
    exact stratHom_coord_ε hY V (q.comp h) (p.comp f) (q.comp f) x
  choose w0 hw0 using fun x => ev _ (hz x)
  let w : N →ₗ[B.A] N' :=
    { toFun := w0
      map_add' := fun x y => by
        apply inj
        show V'.v h f (w0 (x + y)) = V'.v h f (w0 x + w0 y)
        refine (hw0 (x + y)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_add (w0 x) (w0 y)).symm
        refine Eq.trans ?_ (congrArg₂ (· + ·) (hw0 x) (hw0 y)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_add x y)).trans (Matrix.mulVec_add _ _ _)
      map_smul' := fun c x => by
        apply inj
        show V'.v h f (w0 (c • x)) = V'.v h f (c • w0 x)
        refine (hw0 (c • x)).trans ?_
        refine Eq.trans ?_ ((V'.v h f).map_smulₛₗ c (w0 x)).symm
        refine Eq.trans ?_ (congrArg (h.f c • ·) (hw0 x)).symm
        exact (congrArg (Y.map (BK.hf f)).mulVec ((V.v h f).map_smulₛₗ c x)).trans (Matrix.mulVec_smul _ _ _) }
  refine ⟨w, fun Q a g x => ?_⟩
  obtain ⟨Q', h', a', hcomm, hinj⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B C h hc Q a
  have hw : w x = w0 x := rfl
  funext i
  apply hinj
  have lhs : (fun j => h'.f (V'.v a g (w0 x) j)) = V'.v (a'.comp h) (h'.comp g) (w0 x) := by
    exact (funext fun j => (V'.v_nat h' a g (w0 x) j).symm).trans
      (congrArg (fun t => V'.v t (h'.comp g) (w0 x)) hcomm.symm)
  have rhs : (fun j => h'.f (((Y.map (BK.hf g)).mulVec (V.v a g x)) j)) =
      (Y.map (BK.hf (h'.comp g))).mulVec (V.v (a'.comp h) (h'.comp g) x) := by
    exact (stratHom_coord_nat Y V h' a g x).trans
      (congrArg (fun t => (Y.map (BK.hf (h'.comp g))).mulVec (V.v t (h'.comp g) x)) hcomm.symm)
  have mid : V'.v (a'.comp h) (a'.comp f) (w0 x) = (Y.map (BK.hf (a'.comp f))).mulVec (V.v (a'.comp h) (a'.comp f) x) := by
    exact (funext fun j => V'.v_nat a' h f (w0 x) j).trans
      ((congrArg (fun v : Fin d' → C.A => fun j => a'.f (v j)) (hw0 x)).trans (stratHom_coord_nat Y V a' h f x))
  have := congrFun (lhs.trans ((V'.v_ε (a'.comp h) (h'.comp g) (a'.comp f) (w0 x)).trans
    ((congrArg (S'.ε (h'.comp g) (a'.comp f)).mulVec mid).trans
      ((stratHom_coord_ε hY V (a'.comp h) (h'.comp g) (a'.comp f) x).symm.trans rhs.symm)))) i
  rw [hw]
  exact this

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMapStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stratifiedPhiModuleHom_valueMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N'] [Module B.A N'] (V : Eval S B N) (V' : Eval S' B N'), ∃ w : N →ₗ[B.A] N', ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : N), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x) := by
  first | exact @GlobalTheory.BSP.evalHom | exact GlobalTheory.BSP.evalHom | (intros; apply GlobalTheory.BSP.evalHom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem coord_of_frac_rel {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {d : ℕ}
    (b : Module.Basis (Fin d) A N) (b' : Fin d → N) (hb : ∀ i, b i = b' i) (T c : A) (v w : Fin d → A) (n : N) (r s j k : ℕ)
    (h1 : (T * T) ^ r • (T ^ j • ∑ i, v i • b' i - T ^ k • n) = 0)
    (h2 : T ^ s • (c • n - T ^ j • ∑ i, w i • b' i) = 0) :
    T ^ (r + r + s + j) • (c • v - T ^ k • w) = 0 := by
  obtain rfl : ⇑b = b' := funext hb
  apply b.equivFun.symm.injective
  rw [map_zero, map_smul, map_sub, map_smul, map_smul, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply]
  generalize ∑ i, v i • b i = V at *
  generalize ∑ i, w i • b i = W at *
  linear_combination (norm := module) (T ^ s * c) • h1 + (T ^ (r + r + k)) • h2

theorem coord_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  intro l _ K bk d S M e hF B V hV t x m k h Q a g
  refine (exists_isFrac (a.f t) (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩ (M.tr a x))).elim fun n hn => hn.elim fun j hn => ?_
  refine (M.Φ_nat a t ⟨a.f t, a.f_I _ t.2⟩ x m k n j h hn).elim fun r hr => ?_
  refine (GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ Q g ⟨a.f t, a.f_I _ t.2⟩ (V.v a g x) n j
    ((congrArg (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩) (hV a g x)).symm.trans hn)).elim fun s hs => ?_
  refine (GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e).elim fun b hb => ?_
  exact ⟨r + r + s + j, coord_of_frac_rel b (fun i => M.tr g (e i)) hb (a.f t) (BK.hf g bk.E ^ S.a)
    (V.v a g m) ((S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) n r s j k
    ((congrArg (fun z => (a.f t * a.f t) ^ r • (a.f t ^ j • z - a.f t ^ k • n)) (hV a g m)).symm.trans hr) hs⟩

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinatesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedCrystal_frobenius_coordinates : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  first | exact @GlobalTheory.BSP.coord_frobenius | exact GlobalTheory.BSP.coord_frobenius | (intros; apply GlobalTheory.BSP.coord_frobenius <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobenius
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem frob_coord_compat {C : Type} [CommRing C] {d d' : ℕ} (φ : C →+* C) (E T : C) (hE : E ∈ nonZeroDivisors C)
    (A : Matrix (Fin d) (Fin d) C) (A' : Matrix (Fin d') (Fin d') C) (Y : Matrix (Fin d') (Fin d) C)
    (a a' r r' k j : ℕ) (hY : E ^ a • (A' * Y.map φ) = E ^ a' • (Y * A)) (u m : Fin d → C) (n : Fin d' → C)
    (h1 : T ^ r • (E ^ a • m - T ^ k • A.mulVec fun i => φ (u i)) = 0)
    (h2 : T ^ r' • (E ^ a' • n - T ^ j • A'.mulVec fun i => φ (Y.mulVec u i)) = 0) :
    T ^ (r + r') • (T ^ k • n) = T ^ (r + r') • (T ^ j • Y.mulVec m) := by
  have e1 : (fun i => φ (Y.mulVec u i)) = (Y.map φ).mulVec fun i => φ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [e1, Matrix.mulVec_mulVec] at h2
  have h3 := congrArg Y.mulVec h1
  rw [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec,
    Matrix.mulVec_zero] at h3
  have h4 := congrArg (fun Z => Matrix.mulVec Z fun i => φ (u i)) hY
  simp only [Matrix.smul_mulVec] at h4
  funext i
  have h2i := congrFun h2 i
  have h3i := congrFun h3 i
  have h4i := congrFun h4 i
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at h2i h3i h4i ⊢
  rw [← sub_eq_zero]
  refine (mem_nonZeroDivisors_iff.1 (pow_mem hE (a + a'))).1 _ ?_
  linear_combination (T ^ r * T ^ k * E ^ a) * h2i - (T ^ r' * T ^ j * E ^ a') * h3i +
    T ^ (r + r' + k + j) * h4i

theorem eval_map_Φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  intro l _ K bk d d' S S' M e M' e' hF hF' Y hY B V V' hV hV' w hw t x m k hx
  refine (GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B).elim fun C hC => hC.elim fun h hC => hC.1.elim fun g => ?_
  have hc := hC.2
  have hinj := (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' B C (M'.M B) V' h g hc).1
  have hE := (GlobalTheory.T.breuilKisinHom_eisenstein_span_and_nonZeroDivisor l K bk C g).2
  have hnj : ∃ n j, IsFrac (t : B.A) (M'.Φ B t (w x)) n j := by
    induction M'.Φ B t (w x) using LocalizedModule.induction_on with
    | h n s =>
      obtain ⟨_, j, rfl⟩ := s
      exact ⟨n, j, rfl⟩
  refine hnj.elim fun n hn => hn.elim fun j hn => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d S M e hF B V hV t x m k hx C h g).elim fun r h1 => ?_
  refine (GlobalTheory.T.framedCrystal_frobenius_coordinates l K bk d' S' M' e' hF' B V' hV' t (w x) n j hn C h g).elim fun r' h2 => ?_
  rw [hw] at h2
  have hY' : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map C.D.φ) =
      BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    have e1 : (Y.map (BK.hf g)).map C.D.φ = (Y.map (frobS l bk.a)).map (BK.hf g) := by
      ext i j
      exact (g.f_φ (Y i j)).symm
    rw [e1, ← Matrix.map_mul, ← Matrix.map_mul]
    ext i j
    have h5 := congrArg (BK.hf g) (congrFun (congrFun hY.φ i) j)
    simpa only [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, Matrix.map_apply] using h5
  have key := frob_coord_compat C.D.φ _ _ hE _ _ _ _ _ _ _ _ _ hY' _ _ _ h1 h2
  unfold IsFrac at hn ⊢
  rw [hn, LocalizedModule.mk_eq]
  refine ⟨⟨(t : B.A) ^ (r + r'), r + r', rfl⟩, hinj ?_⟩
  simp only [Submonoid.smul_def, LinearMap.map_smulₛₗ, map_pow, hw]
  exact key

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobeniusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (M' : FCrys l ↥(OL K)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)) (V' : Eval S' B (M'.M B)), IsCoord e V → IsCoord e' V' → ∀ w : M.M B →ₗ[B.A] M'.M B, (∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q) (x : M.M B), V'.v a g (w x) = (Y.map (BK.hf g)).mulVec (V.v a g x)) → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → IsFrac (t : B.A) (M'.Φ B t (w x)) (w m) k := by
  first | exact @GlobalTheory.BSP.eval_map_Φ | exact GlobalTheory.BSP.eval_map_Φ | (intros; apply GlobalTheory.BSP.eval_map_Φ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrism
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrism
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.CoordEx

theorem exists_basis {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) {d : ℕ}
    (e : Module.Basis (Fin d) A M) : ∃ b : Module.Basis (Fin d) B N, ∀ i, b i = u (e i) := by
  let v : M →ₛₗ[f] (Fin d → B) :=
    { toFun := fun x i => f (e.repr x i)
      map_add' := fun x y => by ext i; simp
      map_smul' := fun a x => by ext i; simp }
  obtain ⟨S, hS, -⟩ := h _ v
  let Q : (Fin d → B) →ₗ[B] N := Fintype.linearCombination B fun i => u (e i)
  have hQ : Q.comp S = LinearMap.id := h.hom_ext fun x => by
    rw [LinearMap.comp_apply, hS, LinearMap.id_apply, Fintype.linearCombination_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← e.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun i _ => (u.map_smulₛₗ _ _).symm
  have hv : ∀ i, S (u (e i)) = Pi.single i 1 := fun i => by
    rw [hS]
    ext j
    change f (e.repr (e i) j) = _
    by_cases hij : j = i
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hQ1 : ∀ i, Q (Pi.single i 1) = u (e i) := fun i => by
    simp [Q, Fintype.linearCombination_apply_single]
  have hS' : S.comp Q = LinearMap.id := by
    refine (Pi.basisFun B (Fin d)).ext fun i => ?_
    rw [Pi.basisFun_apply, LinearMap.comp_apply, hQ1, hv, LinearMap.id_apply]
  refine ⟨(Pi.basisFun B (Fin d)).map (LinearEquiv.ofLinear Q S hQ hS'), fun i => ?_⟩
  rw [Module.Basis.map_apply, Pi.basisFun_apply, LinearEquiv.ofLinear_apply, hQ1]

theorem equivFun_eq {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {d : ℕ}
    (b : Module.Basis (Fin d) A M) (y : M) (c : Fin d → A) (h : y = ∑ i, c i • b i) : b.equivFun y = c := by
  rw [h, ← b.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e →
    ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  intro l _ K bk d S M e hF B
  have hb : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q), ∃ b : Module.Basis (Fin d) Q.A (M.M Q),
      ∀ i, b i = M.tr g (e i) := fun Q g => exists_basis (M.tr_bc g) e
  choose b hb using hb
  have hs : ∀ (Q : Obj l ↥(OL K)) (g : Hom bk.prism Q) (y : M.M Q),
      y = ∑ i, (b Q g).equivFun y i • M.tr g (e i) := fun Q g y => by
    conv_lhs => rw [← (b Q g).sum_equivFun y]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]
  refine ⟨{ fin := M.fin B
            proj := M.proj B
            v := fun {Q} a g => (b Q g).equivFun.toLinearMap.comp (M.tr a)
            bc := fun {Q} a g => (M.tr_bc a).comp_equiv _
            v_ε := fun {Q} a g g' x => ?_
            v_nat := fun {Q Q'} c a g x i => ?_ }, fun {Q} a g x => hs Q g _⟩
  · change (b Q g).equivFun (M.tr a x) = (S.ε g g').mulVec ((b Q g').equivFun (M.tr a x))
    refine equivFun_eq _ _ _ ?_
    refine (hs Q g' (M.tr a x)).trans ?_
    generalize (b Q g').equivFun (M.tr a x) = c
    simp only [hF.tr g g', Finset.smul_sum, smul_smul, hb, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm (c j)]
  · change (b Q' (c.comp g)).equivFun (M.tr (c.comp a) x) i = c.f ((b Q g).equivFun (M.tr a x) i)
    refine congrFun (equivFun_eq _ _ (fun i => c.f ((b Q g).equivFun (M.tr a x) i)) ?_) i
    refine (M.tr_comp c a x).trans ((congrArg (M.tr c) (hs Q g (M.tr a x))).trans ?_)
    refine (map_sum (M.tr c) _ _).trans (Finset.sum_congr rfl fun j _ => ?_)
    exact ((M.tr c).map_smulₛₗ _ _).trans
      (congrArg (c.f _ • ·) ((hb Q' (c.comp g) j).trans (M.tr_comp c g (e j))).symm)

end GlobalTheory.BSP.CoordEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrismStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.framedFCrystal_exists_coords_every_prism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ B : Obj l ↥(OL K), ∃ V : Eval S B (M.M B), IsCoord e V := by
  first | exact @GlobalTheory.BSP.CoordEx.main | exact GlobalTheory.BSP.CoordEx.main | (intros; apply GlobalTheory.BSP.CoordEx.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHom
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d} {M : FCrys l ↥(OL K)}
  {e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)}

theorem IsCoord.v_eq_of_sum {B Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} (hV : IsCoord e V) (a : Hom B Q)
    (g : Hom bk.prism Q) (x : M.M B) (z : Fin d → Q.A) (hz : M.tr a x = ∑ i, z i • M.tr g (e i)) :
    V.v a g x = z := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e
  have h := (hV a g x).symm.trans hz
  simp only [← hb] at h
  funext i
  have := congrArg (fun y => b.repr y i) h
  simpa [Finsupp.single_apply, Module.Basis.repr_self] using this

theorem IsCoord.v_tr {B B' Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} {V' : Eval S B' (M.M B')}
    (hV : IsCoord e V) (hV' : IsCoord e V') (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B) :
    V'.v a g (M.tr k x) = V.v (a.comp k) g x :=
  hV'.v_eq_of_sum a g _ _ (by rw [← M.tr_comp]; exact hV _ g x)

theorem exists_fHom_of_isStratHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ)
    (S : Strat bk d) (S' : Strat bk d') (M M' : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)),
    Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y →
    ∃ u : FHom M M', ∀ j, u.u bk.prism (e j) = ∑ i, bk.toP (Y i j) • e' i := by
  intro l _ K bk d d' S S' M M' e e' hF hF' Y hY
  choose V hV using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d S M e hF
  choose V' hV' using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d' S' M' e' hF'
  choose w hw using fun B => GlobalTheory.T.exists_stratifiedPhiModuleHom_valueMap l K bk d d' S S' Y hY B (M.M B) (M'.M B) (V B) (V' B)
  refine ⟨⟨w, fun {P P'} k x => ?_, fun P t x m k h =>
    GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius l K bk d d' S S' M e M' e' hF hF' Y hY P (V P) (V' P) (hV P) (hV' P) (w P) (hw P) t x m k h⟩,
    fun j => ?_⟩
  · obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk P'
    apply (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' P' C (M'.M P') (V' P') h f hc).1
    rw [hw, IsCoord.v_tr (hV P) (hV P'), IsCoord.v_tr (hV' P) (hV' P'), hw]
  · have h1 := hV' bk.prism (Hom.id _) (Hom.id _) (w bk.prism (e j))
    have h2 : (V bk.prism).v (Hom.id _) (Hom.id _) (e j) = Pi.single j 1 :=
      IsCoord.v_eq_of_sum (hV _) _ _ _ _ (by simp [M.tr_id, Pi.single_apply])
    have h3 := ((hw bk.prism _ (Hom.id _) (Hom.id _) (e j)).trans (congrArg _ h2)).trans
      (Matrix.mulVec_single_one _ j)
    rw [h3] at h1
    simp only [M'.tr_id] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun c : bk.prism.A => c • e' i) (show ((Y.map (BK.hf (Hom.id bk.prism))).col j) i = bk.toP (Y i j) from rfl)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFCrystalHomOfStratifiedPhiModuleHomStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fCrystalHom_of_stratifiedPhiModuleHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (M M' : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)), Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y → ∃ u : FHom M M', ∀ j, u.u bk.prism (e j) = ∑ i, bk.toP (Y i j) • e' i := by
  first | exact @GlobalTheory.BSP.exists_fHom_of_isStratHom | exact GlobalTheory.BSP.exists_fHom_of_isStratHom | (intros; apply GlobalTheory.BSP.exists_fHom_of_isStratHom <;> assumption)
end
