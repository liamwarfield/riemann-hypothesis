module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreSep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteSumReduction
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.BuildingComponentUniqueness
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.MemCongruenceSubgroupIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConj

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreH
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.coreH :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    H.Out θ a K P (maximalIdeal _) D ψ := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP _ _ _ a K _ _ D ψ hU
  refine ⟨hU, UpperTheory.V.Hi.coreSep hL L Ω l n c H hA A θ hθ ι P hP a K, fun lam hlam y hy => ?_⟩
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy ⊢
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨-, -, -, -, -, hpt, -⟩ :=
    UpperTheory.V.Hi.partAct0 hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ rfl
  obtain ⟨Y, F, e, hY, he, hF0, hF, hop⟩ := hpt y hx
  obtain ⟨hD, hch⟩ := UpperTheory.V.Hi.coreEig hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨Y.r, Y.cont, Y.ss, hY, hD, fun hg v => ?_⟩
  obtain ⟨ω, hsm, hPS, hinv, hU'⟩ := UpperTheory.V.Hi.goodScalB hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp hg Y K e he
    fun h0 => hF0 ((Submodule.mem_bot ℂ).1 (h0 ▸ hF))
  have hO := hch v (ω v) (hsm v) (hinv v) fun j =>
    smul_left_injective ℂ hF0 ((hop (.inr (v, j))).symm.trans ((hU' v j).2 F hF))
  obtain ⟨rc, hrc0⟩ := hL.loc.llc L Ω (H.pl v) (H.Sl v) (H.ovr v)
  have hrc : IsRec (H.ovr v) rc := GlobalTheory.T.rec_of_rec_literal hL.loc.dzc hL.loc.dzi hL.loc.exh hL.loc.multi hL.loc.cos hL.loc.zel
    hL.loc.geo hL.loc.bz L Ω _ _ _ rc hrc0
  obtain ⟨φ⟩ := hPS v
  have hpol := (UpperTheory.V.Hi.psRec hL L Ω n (H.Sl v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v) rc hrc (Y.σl v) (ω v)
    (hsm v)).1 (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hdist : ∀ i j, i ≠ j → ∃ u : Uo ((H.Sl v).adicCompletion L), ω v i u ≠ ω v j u := fun i j hij => by
    obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
  have hdr := Y.atL v (ω v) (hsm v) hdist ⟨φ⟩ rc hrc ((UpperTheory.V.Lev.ssCalc L Ω _ _ (H.ovr v)).1 n _ (fun j => (ω v j).comp (H.art v)) hpol)
  rw [funext hpol] at hdr
  refine UpperTheory.V.Loc.ordFlag hL L Ω l hA.odd ι n (H.Sl v) (hA.Sl_over v) (H.pl v) (H.ovr v) (H.art v) (hA.art_spec v)
    _ (Y.cont.comp (hA.prj_cont.comp continuous_subtype_val)) (htW lam) (fun τ i j hij => ?_) (ω v) _ hO
    (fun i j hij => ?_) hdr
  · have h1 := (lam τ).anti (Fin.rev_le_rev.2 hij.le)
    have h2 : (i : ℕ) < j := hij
    simp only [htW, lowW]
    omega
  · obtain ⟨u, hu⟩ := hg.2.2 v i j hij
    refine ⟨u, fun h0 => hu (ι.injective (mul_left_cancel₀ (ω v j u).ne_zero ?_))⟩
    rw [hinv v j u, ← h0, hinv v i u]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.FreeOfNeat
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace UpperTheory.V.Hi.LvR

section Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid V0.frame O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

theorem c1 (i) : (rUp h).chib i = (r.chib i).comp (fh h).π₀ := rfl

theorem rUp_chib (i) (g : V.frame.G₀) : (rUp h).chib i g = r.chib i (p0 h g) := MonoidHom.comp_apply (r.chib i) (p0 h) g

theorem c2 (v i) : (rUp h).psib v i = (r.psib ((fh h).vl v) i).comp ((fh h).gv v) := MonoidHom.ext fun _ => rfl

theorem c3 (v i) (g : V.frame.mu v) (hg : (fh h).gv v g ∈ V0.frame.mu ((fh h).vl v)) : (rUp h).th v i g = r.th ((fh h).vl v) i ⟨_, hg⟩ := by
  have e : ∀ g : W.muG l (Dec (F := L) (s.A v.1)), (rUp h).th v i g = @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) g := fun _ => rfl
  have e2 : ∀ (g : Dec (F := L) (s.A v.1)) (hg : g ∈ W.muG l (Dec (F := L) (s.A v.1))), @id (W.muG l (Dec (F := L) (s.A v.1)) →* Oˣ) (r.th v i) ⟨g, hg⟩ = r.th v i ⟨g, hg⟩ := fun _ _ => rfl
  exact (e g).trans (e2 g.1 (@id (g.1 ∈ W.muG l (Dec (F := L) (s.A v.1))) g.2))

theorem c4 (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (u : s.St) (g : V.η.ker) (hg : g ∈ (rUp h).Ip u) : p0 h g ∈ r.Ip u := by
    obtain ⟨⟨x, hx, rfl⟩, h2⟩ := hg
    refine ⟨⟨x, hx, (levelChangeBaseGroupHom_apply_projection h hp x).symm⟩, ?_⟩
    exact Subgroup.mem_iInf.2 fun i => MonoidHom.mem_ker.2 ((rUp_chib h i _).symm.trans (MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 h2 i)))

theorem rUp_compat (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) : (fh h).Compat (rUp h) r :=
  ⟨c1 h, c2 h, c3 h, fun u g hg => Or.inr ⟨u, c4 h hp u g hg⟩⟩

theorem pairUp (hn : 1 ≤ n) (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) :
    ∃ p' : Pair (rUp h) R, p'.D = p.D.comap (p0 h) ∧ ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* Rˣ) (p'.ψ v i) (p.ψ v i) := by
  obtain ⟨p', h1, h2⟩ := W.exists_determinantPair_pullback l _ _ (fh h) O n (rUp h) r (rUp_compat h hp) (fun e => by omega) R p
  exact ⟨p', h1, fun v i => Eq.trans (h2 v i) rfl⟩

end Gen

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V0.frame c.O n} {V : s.Lev}
  (h : (Pa.globOf r V).Hom (Pa.globOf r V0))

abbrev qUp (V : s.Lev) {q : ℕ} (w : Fin q → Plc L) (h1 : Function.Injective fun j => (w j).under (𝓞 (Lp L)))
    (h2 : ∀ j, (w j).under (𝓞 (Lp L)) ∉ s.S) (h3 : V.S' = s.S ∪ Set.range fun j => (w j).under (𝓞 (Lp L))) : QData V where
  Q := Fin q
  wq := w
  inj := h1
  notS := h2
  range := h3

variable (Q0 : QData V0) (Q : QData V) (hS : V0.S' ⊆ V.S')

def opUp {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Op → (hset Q0 τ₀).Op
  | .inl x => .inl (⟨x.1.1, fun h => x.1.2.1 (hS h), x.1.2.2⟩, x.2)
  | .inr x => .inr x

def kMax {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) : (hset Q τ₀).Lev :=
  ⟨fun _ => KO _ (Fin n), fun _ => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩

theorem free_of_neat {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ) (U : Subgroup X.Ub) (hU : X.Neat U) : X.Free τ θ U := by
  intro g γ u hu b hb e
  obtain ⟨rfl, rfl⟩ := hU g γ u hu b hb e
  refine ⟨one_mem _, one_mem _, ?_⟩
  have e1 : ∀ hh, (⟨1, hh⟩ : X.I.T) = 1 := fun _ => rfl
  rw [e1, map_one, map_one]
  simp

theorem teich_ext {O : Type} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] (x y : Oˣ) (h : residue O x = residue O y)
    (hx : x ^ (Nat.card (ResidueField O) - 1) = 1) (hy : y ^ (Nat.card (ResidueField O) - 1) = 1) : x = y := by
  set N := Nat.card (ResidueField O) - 1 with hN
  have hx' : (x : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hx, Units.val_one]
  have hy' : (y : O) ^ N = 1 := by rw [← Units.val_pow_eq_pow_val, hy, Units.val_one]
  have e := (Commute.all (x : O) y).geom_sum₂_mul N
  rw [hx', hy', sub_self] at e
  have hu : IsUnit (∑ i ∈ Finset.range N, (x : O) ^ i * (y : O) ^ (N - 1 - i)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← residue_ne_zero_iff_isUnit, map_sum]
    have : ∀ i ∈ Finset.range N, residue O ((x : O) ^ i * (y : O) ^ (N - 1 - i)) = residue O y ^ (N - 1) := fun i hi => by
      rw [map_mul, map_pow, map_pow, h, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hi
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine mul_ne_zero ?_ (pow_ne_zero _ ((residue_ne_zero_iff_isUnit _).2 y.isUnit))
    haveI := Fintype.ofFinite (ResidueField O)
    rw [hN, Nat.cast_sub Nat.card_pos, Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero]
    simp
  exact Units.ext (sub_eq_zero.1 (hu.mul_right_eq_zero.1 e))

theorem typeFor_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ht : TypeFor r ι τ₀) : TypeFor (rUp h) ι τ₀ := by
  intro t' ht'
  haveI : Finite (ResidueField c.O) := Module.finite_of_finite (ResidueField ℤ_[l])
  have hk : ∀ i, (p0 h).ker ≤ (t' i).ker := fun i g hg => by
    refine teich_ext _ _ ?_ (ht' i g).2 (one_pow _)
    rw [(ht' i g).1, rUp_chib, MonoidHom.mem_ker.1 hg, map_one]
    simp
  let t : Fin n → V0.frame.G₀ →* c.Oˣ := fun i => (p0 h).liftOfSurjective (surjective_levelChangeBaseGroupHom h) ⟨t' i, hk i⟩
  have e : ∀ i g, t i (p0 h g) = t' i g := fun i g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have := ht t fun i g => by
    obtain ⟨x, rfl⟩ := surjective_levelChangeBaseGroupHom h g
    rw [e, ← rUp_chib]
    exact ht' i x
  have e2 : ∀ (u : s.St) i, (t' i).comp (V.pr.comp (Ine (F := L) (s.A u)).subtype) =
      (t i).comp (V0.pr.comp (Ine (F := L) (s.A u)).subtype) := fun u i => MonoidHom.ext fun x =>
    (e i (V.pr x)).symm.trans (congrArg (t i) (levelChangeBaseGroupHom_apply_projection h hp x))
  simp only [e2]
  exact this

theorem cont_up {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O) {A : Type} [CommRing A] [IsLocalRing A]
    (θ : (hset Q0 τ₀).X.I.T →* Aˣ) (hθ : (hset Q0 τ₀).X.I.ContChar θ) : (hset Q τ₀).X.I.ContChar θ := hθ

theorem res_up (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) {m : ℕ} (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (a : (hset Q0 τ₀).Op → c.O) (ha : IsRes Q0 r τ₀ a) : IsRes Q (rUp h) τ₀ fun i => a (opUp Q0 Q hS τ₀ i) := by
  refine ⟨fun w B σ hB hσ => ?_, ?_⟩
  · refine (congrArg (fun D : W.GDet n (ResidueField c.O) V.frame.G₀ => D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1))
      (rUp_Dbar h)).trans ((chi_comap r.Dbar (p0 h) (V.pr σ⁻¹)).trans ?_)
    exact (congrArg (fun g : V0.frame.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) (levelChangeBaseGroupHom_apply_projection h hp σ⁻¹)).trans
      (ha.frob ⟨w.1, fun h => w.2.1 (hS h), w.2.2⟩ B σ hB hσ)
  · have := ha.unif
    cases r
    exact this


end UpperTheory.V.Hi.LvR
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Faith
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.V.Hi.levelUR2Faith :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V : s.Lev) (Q : QData V) [DecidableEq Q.Q] (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (K : (hset Q τ₀).Lev) (k : GV n Q.wq) (j : GV n Q.wq →* Ub n s), (∀ q g, j (Pi.mulSingle q g) = sec n s (Q.wq q) g) → j k ∈ (hset Q τ₀).lev K → k ∈ Subgroup.pi Set.univ K.1 := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q _ c m τ₀ K k j hj hk
  have hS : ∀ q : Q.Q, (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := fun q => by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsec := fun q : Q.Q => (secU l L Ω s n hn (Q.wq q)
    (UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ (hS q)) _ rfl)).2 (Q.notS q)
  have h1 : ∀ (q : Q.Q) (g : GLw n (Q.wq q)) (w : Plc L), w.under (𝓞 (Lp L)) ≠ (Q.wq q).under (𝓞 (Lp L)) →
      CaseU.cmp n w ((sec n s (Q.wq q) g : Ub n s) : Ga l L n) = 1 := fun q g w hw =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ((hsec q).2.2 g) w) hw)
  have key : ∀ q : Q.Q, ((CaseU.cmp n (Q.wq q)).comp (Ub n s).subtype).comp j =
      Pi.evalMonoidHom (fun q : Q.Q => GLw n (Q.wq q)) q := fun q => by
    refine MonoidHom.pi_ext fun q' g => ?_
    change CaseU.cmp n (Q.wq q) ((j (Pi.mulSingle q' g) : Ub n s) : Ga l L n) =
      (Pi.mulSingle q' g : ∀ q : Q.Q, GLw n (Q.wq q)) q
    rw [hj]
    by_cases h : q = q'
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact (hsec q).2.1 g
    · rw [Pi.mulSingle_eq_of_ne h]
      exact h1 q' g _ fun h' => h (Q.inj h')
  intro q _
  have h2 := (levelUR2LevOut l L Ω s n hn V Q c m τ₀ K (j k) hk).2 q
  have h3 : CaseU.cmp n (Q.wq q) ((j k : Ub n s) : Ga l L n) = k q := DFunLike.congr_fun (key q) k
  rw [h3] at h2
  exact h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Unr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem unr_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem unr_sum {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (t : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, t 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2Unr :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsUnramU σ w := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ _ hY w hw
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hF0
  have hA : F i ∈ (hset Q τ₀).X.AF ξ := hB.1 i (Set.mem_univ _)
  have h1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1 (F i) hA
  obtain ⟨ℓ, hℓ⟩ := not_forall.1 (mt h1 hi)
  refine ⟨_, hσ i ℓ, hℓ, fun x hx hk => ?_⟩
  have hne : ∀ u : Plc L, u.under (𝓞 (Lp L)) ∈ V.S' → cLoc u x = 1 := fun u hu =>
    GlobalTheory.DefU.LocRet.mem_locU_ne hx fun h => hw (h ▸ hu)
  have hS : ∀ v ∈ s.S, cLoc (s.w v) x = 1 := fun v hv => hne _ ((unr_under s v).symm ▸ V.sub hv)
  have hK : cLoc w x ∈ KO (w.adicCompletion L) (Fin n) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact hk
  have h2 := partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB x (Subgroup.mem_inf.1 hx).1
    (fun v => hS v.1 (Or.inl v.2)) 1 (fun u => (hS u.1 (Or.inr (Or.inl u.2))).symm)
    (by
      rw [hS s.v0 (Or.inr (Or.inr rfl))]
      exact one_mem _)
    (fun u _ => by
      by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
      · exact UpperTheory.mem_maximalCompact_of_under_eq L n x w u h hK
      · rw [show cLoc u x = 1 from GlobalTheory.DefU.LocRet.mem_locU_ne hx h]
        exact one_mem _)
    (fun q => hne _ (Q.range.ge (Or.inr ⟨q, rfl⟩))) i ℓ
  exact (unr_sum _ (fun j => RU L n x (toForm ι e (F j) ℓ)) i).symm.trans h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2Sph
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem form_inj {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (hs : Function.Surjective fun k : finU (E := L) (n := n) =>
      (((away l L n).rangeRestrict k, fun v : V.frame.Vl => cLoc (s.w v.1) k) : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1)))
    (F F' : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) (h : ∀ ℓ, toForm ι e F ℓ = toForm ι e F' ℓ) :
    F = F' := by
  funext y
  obtain ⟨k, rfl⟩ := hs y
  refine e.injective ?_
  have hR : ∀ u, infRep (V := V) ι lam k (infRep (V := V) ι lam (k : UA L n)⁻¹ u) = u := fun u => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine (hR _).symm.trans (Eq.trans (congrArg _ ?_) (hR _))
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun ℓ => ?_)
  rw [map_sub]
  exact sub_eq_zero.2 (congrFun (h ℓ) k)

private noncomputable def formLin {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} (V : s.Lev) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) (d : ℕ)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (m : ℕ) (i : Fin m)
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) where
  toFun F := toForm ι e (F i) ℓ
  map_add' F F' := funext fun g => by
    simp only [toForm, Pi.add_apply, map_add (f := _)]
  map_smul' a F := funext fun g => by
    simp only [toForm, Pi.smul_apply, map_smul, RingHom.id_apply]

private theorem push (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (M : Type) [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GLw n w) M) (M' : Type) [AddCommGroup M'] [Module ℂ M'] (ρ' : Representation ℂ (GLw n w) M')
    (σ : Submodule ℂ M') (τ : SmIrr (GLw n w)) (hiso : IsoSum ρ' σ τ) (j : ℕ) (a : ℂ)
    (ha : ∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) (f : M →ₗ[ℂ] M')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (F : M) (hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), ρ k F = F) (hm : f F ∈ σ) :
    f (sphOp ρ j F) = f (a • F) := by
  have h3 := (UpperTheory.V.Hi.partUR2Abs L n w M ρ ⊥ τ bot_le).2.2.1 M' ρ' f.toAddMonoidHom hf j F
  have h2 := (UpperTheory.V.Hi.partUR2Abs L n w M' ρ' σ τ hiso).2.1 j a ha (f F)
    (Submodule.mem_inf.2 ⟨hm, fun k hk => (hf k F).symm.trans (congrArg f (hfix k hk))⟩)
  exact h3.trans (h2.trans (f.map_smul a F).symm)

theorem UpperTheory.V.Hi.partUR2Sph :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → IsSplitAt w → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ →
    ∀ (j : ℕ) (a : ℂ), (∀ v ∈ fixd τ.ρ (KO (w.adicCompletion L) (Fin n)), sphOp τ.ρ j v = a • v) → ∀ F ∈ YOf Q ι τ₀ e ξ σ, sphOp ((hset Q τ₀).atW ι d w) j F = a • F := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hAx w hw hsp τ hτ j a ha F hF
  obtain ⟨j0, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn w hsp).1
  have hS : w.under (𝓞 (Lp L)) ∉ s.S := fun h => hw (Q.range ▸ Or.inl h)
  have hat := UpperTheory.V.Hi.partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ w hsp hS j0 hj1 hj2
  obtain ⟨hB, hm⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ w j0 hj1 hj2 hj3 τ hτ
  have hs := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ (fun _ => rfl)).2.2.2.1
  have hfix : ∀ k ∈ KO (w.adicCompletion L) (Fin n), (hset Q τ₀).atW ι d w k F = F := fun k hk =>
    hB.2 _ (hAx.W_le w ⟨hw, hsp⟩ (Subgroup.mem_map_of_mem _ hk))
  funext i
  refine form_inj V ι lam d e hs _ _ fun ℓ => ?_
  exact push L n w (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) ((hset Q τ₀).atW ι d w) _
    ((RU L n).comp j0) σ τ hiso j a ha (formLin V ι lam d e m i ℓ) (fun g v => hat v g i ℓ) F hfix (hm i ℓ)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.AutomorphicTensorInductionOfLocalPlaces
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem neu_comm {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {w : Plc L} {j : GLw n w →* UA L n}
    (hj : ∀ x ∈ locU n w, x = j (cLoc w x)) {g y : UA L n} (hg : cLoc w g = 1) (hy : y ∈ locU n w) : Commute g y := by
  have h1 : (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = 1 := by
    rw [hj _ (GlobalTheory.DefU.LocRet.ret w n g).2]
    have : cLoc w (GlobalTheory.DefU.LocRet.ret w n g : UA L n) = cLoc w g := GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq rfl g
    rw [this, hg, map_one]
  have h2 := GlobalTheory.DefU.LocRet.commute_ret g ⟨y, hy⟩
  rwa [h1, inv_one, one_mul] at h2

private theorem ne_J {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {St : Type} [Fintype St] [DecidableEq St]
    {wt : St → Plc L} (hinj : Function.Injective fun u => (wt u).under (𝓞 (Lp L))) (j : ∀ u, GLw n (wt u) →* UA L n)
    (h1 : ∀ u g, j u g ∈ locU n (wt u)) (h2 : ∀ u g, cLoc (wt u) (j u g) = g) (h3 : ∀ u, ∀ x ∈ locU n (wt u), x = j u (cLoc (wt u) x)) :
    ∃ J : GV n wt →* UA L n, (∀ u g, J (Pi.mulSingle u g) = j u g) ∧ (∀ g, J g ∈ GlobalTheory.UnitaryBC.finU (E := L) (n := n)) ∧
      (∀ g u, cLoc (wt u) (J g) = g u) ∧
      (∀ g (v : Plc L), (∀ u, v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L))) → cLoc v (J g) = 1) ∧
      ∀ g k, (∀ u, cLoc (wt u) k = 1) → Commute k (J g) := by
  have h4 : ∀ u g (v : Plc L), v.under (𝓞 (Lp L)) ≠ (wt u).under (𝓞 (Lp L)) → cLoc v (j u g) = 1 := fun u g v hv =>
    GlobalTheory.DefU.LocRet.mem_locU_ne (h1 u g) hv
  have hc : Pairwise fun a b => ∀ x y, Commute (j a x) (j b y) := fun a b hab x y =>
    neu_comm (h3 b) (h4 a x _ fun e => hab (hinj e).symm) (h1 b y)
  let J := MonoidHom.noncommPiCoprod j hc
  have hJ : ∀ u g, J (Pi.mulSingle u g) = j u g := fun u g => MonoidHom.noncommPiCoprod_mulSingle j u g
  have key : ∀ P : Subgroup (UA L n), (∀ u g, j u g ∈ P) → ∀ g, J g ∈ P := fun P hP g => by
    have : J.range ≤ P := by
      rw [MonoidHom.noncommPiCoprod_range]
      exact iSup_le fun u => by rintro _ ⟨g, rfl⟩; exact hP u g
    exact this ⟨g, rfl⟩
  refine ⟨J, hJ, key _ fun u g => (h1 u g).1, fun g u => ?_, fun g v hv => key (cLoc v).ker (fun u g => h4 u g v (hv u)) g,
    fun g k hk => ?_⟩
  · have : (cLoc (wt u)).comp J = Pi.evalMonoidHom (fun u => GLw n (wt u)) u := MonoidHom.pi_ext fun i x => by
      rw [MonoidHom.comp_apply, hJ, Pi.evalMonoidHom_apply]
      by_cases h : u = i
      · subst h
        rw [h2, Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h]
        exact h4 i x _ fun e => h (hinj e)
    exact DFunLike.congr_fun this g
  · exact (Subgroup.mem_centralizer_singleton_iff.1
      (key (Subgroup.centralizer {k}) (fun u g => Subgroup.mem_centralizer_singleton_iff.2
        (neu_comm (h3 u) (hk u) (h1 u g)).symm.eq) g)).symm

private theorem automorphic_tensor_induction_of_local_places {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {n m : ℕ}
    {St : Type} {wt : St → Plc L} {At : St → ValuationSubring Ω} (ht : ∀ u, IsPlaceOver (At u) (wt u))
    (j : ∀ u, GLw n (wt u) →* UA L n) (J : GV n wt →* UA L n)
    (hJ : ∀ u g, J (by classical exact MonoidHom.mulSingle (fun u => GLw n (wt u)) u g) = j u g)
    (τ₀ : KT n wt →* GL (Fin m) ℂ) (χ : ∀ u, Fin n → Ine (F := L) (At u) →* ℂˣ) (hT : IsType ht τ₀ χ)
    {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ) (τ : ∀ u, SmIrr (GLw n (wt u)))
    (hτ : ∀ u, IsoSum ((RU L n).comp (j u)) σ (τ u)) (F : Fin m → UA L n → ℂ) (hF0 : F ≠ 0) (hF1 : ∀ i, F i ∈ σ)
    (hF2 : ∀ (k : KT n wt) i, ∑ a, τ₀ k i a • RU L n (J k) (F a) = F i) :
    ∀ u rc, IsRec (ht u) rc → IsTypeWD (ht u) (χ u) (rc (algNorm (τ u))) := by
  haveI : Nontrivial σ := Submodule.nontrivial_iff_ne_bot.2 hσ.ne_bot
  let ρ : Representation ℂ (GV n wt) σ :=
    (⟨σ, fun g v hv => hσ.stable (J g) v hv⟩ : Subrepresentation ((RU L n).comp J)).toRepresentation
  have hρ : ∀ g (y : σ), (ρ g y : UA L n → ℂ) = RU L n (J g) y := fun _ _ => rfl
  refine (hT.2 σ ρ τ fun u => ?_).1 ⟨fun i => ⟨F i, hF1 i⟩, fun h => hF0 (funext fun i => congrArg Subtype.val (congrFun h i)),
    fun k i => Subtype.ext ?_⟩
  · refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ _ ⊤ σ (τ u) Unit (fun _ => σ.subtype) (hτ u) (fun _ _ _ => Submodule.mem_top)
      (fun _ y _ => y.2) (fun _ g y _ => ?_) fun y _ h => Subtype.ext (h ())
    exact (hρ _ y).trans (by rw [hJ]; rfl)
  · change σ.subtype (∑ a, τ₀ k i a • ρ k ⟨F a, hF1 a⟩) = F i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hF2 k i]
    rfl

theorem UpperTheory.V.Hi.partUR2Type :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ χ : ∀ u : s.St, Fin n → Ine (F := L) (s.A u) →* ℂˣ, IsType (fun u : s.St => s.hw u) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) χ →
    ∀ τ : ∀ u : s.St, SmIrr (GLw n (s.w u)), (∀ u : s.St, IsCompAlong σ (locU n (s.w u)) ((cLoc (s.w u)).comp (locU n (s.w u)).subtype) (τ u).ρ) → ∀ (u : s.St) rc, IsRec (s.hw u) rc → IsTypeWD (s.hw u) (χ u) (rc (algNorm (τ u))) := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ he σ hσ hY χ hT τ hτ
  letI : DecidableEq s.St := fun a b => Classical.propDecidable _
  obtain ⟨hw, hsp⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  choose j h1 h2 _ h3 using fun u : s.St => (secU l L Ω s n hn (wt s u) (hsp _ (by
    rw [hw]
    exact s.split _ (Or.inr (Or.inl u.2))))).1
  obtain ⟨J, hJ, j1, j2, j3, -⟩ := ne_J (wt := wt s)
    (fun a b hab => Subtype.ext ((hw _).symm.trans (hab.trans (hw _)))) j h1 h2 h3
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hFσ⟩ := (partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have f1 := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ he _ fun _ => rfl).1
  have hex : ∃ i ℓ, toForm ι e (F i) ℓ ≠ 0 := by
    by_contra h
    exact hF0 (funext fun i => f1 (F i) (hB.1 i trivial) fun ℓ => by
      by_contra h'
      exact h ⟨i, ℓ, h'⟩)
  obtain ⟨i₀, ℓ, hℓ⟩ := hex
  have j4 : ∀ g (v : Plc L), v.under (𝓞 (Lp L)) ∉ s.St → cLoc v (J g) = 1 := fun g v hv =>
    j3 g v fun a h => hv (by rw [h, hw]; exact a.2)
  refine automorphic_tensor_induction_of_local_places (fun u : s.St => s.hw u) j J (fun u g => ?_) _ χ hT hσ τ
    (fun u => UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ (j u) (h1 u) (h2 u) (h3 u) (τ u) (hτ u)) (fun i => toForm ι e (F i) ℓ)
    (fun h => hℓ (congrFun h i₀)) (fun i => hFσ i ℓ) fun k i => ?_
  · exact hJ u g
  · refine partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ he F hB (J k) (j1 _) (fun v => j4 _ _ ?_) k (fun u => (j2 _ u).symm) ?_
      (fun w hw' => ?_) (fun q => j4 _ _ fun h => Q.notS q (Or.inr (Or.inl h))) i ℓ
    · rw [hw]
      exact fun h => s.St_l _ h v.2
    · rw [j4 _ _ (by rw [hw]; exact s.v0_St)]
      exact one_mem _
    · rw [j4 _ _ fun h => hw' (V.sub (Or.inr (Or.inl h)))]
      exact one_mem _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LNotMemBasePrime
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem w_under {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)

private theorem l_not_mem_base_prime {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (s : HidaSetting l L Ω) : ((l : ℕ) : 𝓞 (Lp L)) ∉ s.v0.asIdeal := by
  intro h
  have h1 : ((s.p : ℕ) : 𝓞 (Lp L)) ∈ s.v0.asIdeal := by
    rw [← s.norm_v0_eq_one]
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using
      Ideal.absNorm_mem s.v0.asIdeal
  have hc : IsCoprime (s.p : 𝓞 (Lp L)) (l : 𝓞 (Lp L)) :=
    ((Nat.coprime_primes s.p_prime Fact.out).2 s.p_ne).cast
  obtain ⟨a, b, hab⟩ := hc
  exact s.v0.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (hab ▸ add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h)))

private theorem sum_one {M : Type} [AddCommGroup M] [Module ℂ M] {m : ℕ} {H : Type} [Group H] (τ : H →* GL (Fin m) ℂ)
    (f : Fin m → M) (i : Fin m) : ∑ j : Fin m, τ 1 i j • f j = f i := by
  simp [Matrix.one_apply]

theorem UpperTheory.V.Hi.partUR2V0 :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    YOf Q ι τ₀ e ξ σ ≠ ⊥ → ∀ τ : SmIrr (GLw n (s.w s.v0)), IsCompAlong σ (locU n (s.w s.v0)) ((cLoc (s.w s.v0)).comp (locU n (s.w s.v0)).subtype) τ.ρ → fixd τ.ρ (Kc _ n 1) ≠ ⊥ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hY τ hτ
  have hw0 := w_under s s.v0
  have hsp : IsSplitAt (s.w s.v0) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA s.v0) (s.split _ (Or.inr (Or.inr rfl))) _ hw0
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (UpperTheory.V.Hi.secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  obtain ⟨h1, -, -, h4⟩ := UpperTheory.V.Hi.partUR2Abs L n _ _ _ _ τ hiso
  refine h1 _ (h4 1) ?_
  obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
  obtain ⟨hB, hM⟩ := (UpperTheory.V.Hi.partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ F).1 hF
  have hinj := (UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  intro hbot
  refine hF0 (funext fun i => hinj (F i) (And.left hB i (Set.mem_univ i)) fun ℓ => ?_)
  refine (Submodule.eq_bot_iff _).1 hbot _ (Submodule.mem_inf.2 ⟨hM i ℓ, fun g hg => ?_⟩)
  have hloc : ∀ u : Plc L, u.under (𝓞 (Lp L)) ≠ s.v0 → cLoc u (j g) = 1 := fun u hu =>
    MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 (hj1 g)).2 u) (hw0.symm ▸ hu))
  have h := UpperTheory.V.Hi.partUR2Fix l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ F hB (j g) (Subgroup.mem_inf.1 (hj1 g)).1
    (fun v => hloc _ fun h => l_not_mem_base_prime s (by
      rw [← h, w_under]
      exact v.2)) 1
    (fun u => (hloc _ fun h => s.v0_St (by
      rw [← h, w_under]
      exact u.2)).symm)
    ((hj2 g).symm ▸ hg)
    (fun w hw => by
      rw [hloc w fun h => hw (V.sub (Or.inr (Or.inr h)))]
      exact one_mem _)
    (fun q => hloc _ fun h => Q.notS q (Or.inr (Or.inr h))) i ℓ
  exact (sum_one _ (fun j' => RU L n (j g) (toForm ι e (F j') ℓ)) i).symm.trans h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartUR2IsoQ
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem raF_big {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (ξ : Gp →* GL (Fin d) ℂ) (U : Subgroup X.Ub) (x : X.Ub) (hx : ∀ u ∈ U, Commute u x)
    (F : Fin m → X.Fn ℂ d) (hF : F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U) :
    X.raF d τ x F ∈ Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U := by
  refine ⟨fun i _ => ?_, fun u hu => ?_⟩
  · have h : X.raF d τ x F i = ∑ j, (τ x : Matrix (Fin m) (Fin m) ℂ) i j • fun g => F j (g * ((x : Ga), 1)) := by
      funext g k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    change X.raF d τ x F i ∈ X.AF ξ
    rw [h]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ fun γ g => ?_
    have := hF.1 j trivial γ (g * ((x : Ga), 1))
    simpa only [mul_assoc] using this
  · rw [← Module.End.mul_apply, ← map_mul, (hx u hu).eq, map_mul, Module.End.mul_apply, hF.2 u hu]

private theorem big_atW {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax) (ι : Qbar l ≃+* ℂ) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ)
    (q : H.Q) (g : GLw n (H.wq q)) (F : Fin H.m → H.X.Fn ℂ d) (hF : F ∈ H.Big ι ξ) : H.atW ι d (H.wq q) g F ∈ H.Big ι ξ :=
  raF_big H.X (H.τC ι) ξ H.UQ (H.sec (H.wq q) g) (fun u hu => hA.Q_UQ q u hu g) F hF

private noncomputable def formL {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {n : ℕ} {V : s.Lev} (ι : Qbar l ≃+* ℂ) {lam : Wt L l n} {d : ℕ}
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
  LinearMap.mk₂ ℂ (toForm ι e)
    (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add (f := _)])
    (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
    (fun F ℓ ℓ' => rfl) (fun a F ℓ => rfl)

theorem UpperTheory.V.Hi.partUR2IsoQ :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l) (ι : Qbar l ≃+* ℂ) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (lam : Wt L l n) (d : ℕ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ), IsBasis ι e ξ →
    ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    (hset Q τ₀).Ax → ∀ (q : Q.Q) (τ : SmIrr (GLw n (Q.wq q))), IsCompAlong σ (locU n (Q.wq q)) ((cLoc (Q.wq q)).comp (locU n (Q.wq q)).subtype) τ.ρ → IsoSum ((hset Q τ₀).atW ι d (Q.wq q)) (YOf Q ι τ₀ e ξ σ) τ := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V Q c ι m τ₀ lam d e ξ hξ σ hσ hA q τ hτ
  have hS' : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
    rw [Q.range]
    exact Or.inr ⟨q, rfl⟩
  have hsp : IsSplitAt (Q.wq q) := UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω _ _ (s.hA _) (V.split _ hS') _ rfl
  obtain ⟨j, hj1, hj2, -, hj3⟩ := (secU l L Ω s n hn _ hsp).1
  have hiso := UpperTheory.isoSum_restriction_of_local_component_unitary L n σ hσ _ j hj1 hj2 hj3 τ hτ
  have hmem := partUR2Mem l L Ω s n hn V Q c ι m τ₀ lam d e ξ σ
  have hat := partUR2AtW l L Ω s n hn V Q c ι m τ₀ lam d e ξ hξ _ hsp (Q.notS q) j hj1 hj2
  have hinj := (formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ _ fun _ => rfl).1
  let b := ((Pi.basisFun ℂ (Fin d)).map e).dualBasis
  let φ : Fin m × Fin d → (Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) :=
    fun x => ((formL ι e).flip (b x.2)).comp (LinearMap.proj x.1)
  refine UpperTheory.isoSum_of_injective_equivariant_family _ _ _ _ ((RU L n).comp j) _ σ τ (Fin m × Fin d) φ hiso (fun g F hF => ?_) (fun x F hF => ?_)
    (fun x g F _ => ?_) (fun F hF h0 => ?_)
  · obtain ⟨h1, h2⟩ := (hmem F).1 hF
    refine (hmem _).2 ⟨big_atW (hset Q τ₀) hA ι ξ q g F h1, fun i ℓ => ?_⟩
    refine (hat F g i ℓ).symm ▸ ?_
    exact hσ.stable _ _ (h2 i ℓ)
  · exact ((hmem F).1 hF).2 x.1 (b x.2)
  · exact hat F g x.1 (b x.2)
  · refine funext fun i => hinj (F i) (((hmem F).1 hF).1.1 i trivial) fun ℓ => ?_
    have h : formL ι e (F i) = 0 := b.ext fun k => h0 (i, k)
    exact LinearMap.congr_fun h ℓ
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2BaseEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem cu_ext {Γ R : Type} [TopologicalSpace Γ] [CommRing R] (I : Ideal R) [IsHausdorff I R] {S : Set Γ}
    (hS : Dense S) {f g : Γ → R} (hf : Alg.AdicCont I f) (hg : Alg.AdicCont I g) (h : ∀ x ∈ S, f x = g x) : f = g := by
  funext x
  refine IsHausdorff.eq_iff_smodEq (I := I).2 fun N => ?_
  rw [smul_eq_mul, Ideal.mul_top]
  letI : TopologicalSpace (R ⧸ I ^ N) := ⊥
  haveI : DiscreteTopology (R ⧸ I ^ N) := ⟨rfl⟩
  exact congrFun (Continuous.ext_on hS (hf N).continuous (hg N).continuous fun y hy => by simp only [h y hy]) x

private theorem cu_prod {n : ℕ} {M : Type} [CommGroup M] (f g : Fin n → M)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) : ∀ j, f j = g j := by
  intro j
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have hj : j ∈ Finset.univ.filter fun i => i ≤ j := by simp
    have e := h j
    rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ g hj,
      Finset.prod_congr rfl (g := g) fun i hi => ih i (by
        rw [Finset.mem_erase, Finset.mem_filter] at hi
        exact lt_of_le_of_ne hi.2.2 hi.1)] at e
    exact mul_right_cancel e

private theorem cu_gen {W M k : Type} [Group W] [Group M] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (a : W →* kˣ) (ha : Function.Surjective a) (f g : W →* M)
    (h1 : ∀ s (y : Uo k), a s = y → f s = g s) (h2 : ∀ s, a s = Hi.unif k → f s = g s) (s : W) : f s = g s := by
  obtain ⟨p, hp⟩ := ha (Hi.unif k)
  have e := h1 (s * (p ^ ord k (a s))⁻¹) ⟨_, GlAx.val_div_ord (a s)⟩ (by
    rw [map_mul, map_inv, map_zpow, hp]
    exact (div_eq_mul_inv _ _).symm)
  rw [map_mul, map_mul, map_inv, map_inv, map_zpow, map_zpow, h2 p hp] at e
  exact mul_right_cancel e

private theorem push_cont {Γ O T T₀ : Type} [TopologicalSpace Γ] [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T]
    [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀] (φ : T →ₐ[O] T₀) {f : Γ → T}
    (hf : Alg.AdicCont (maximalIdeal T) f) : Alg.AdicCont (maximalIdeal T₀) fun g => φ (f g) := fun N => by
  have hle : maximalIdeal T ^ N ≤ (maximalIdeal T₀ ^ N).comap (φ : T →+* T₀) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show φ y ∈ maximalIdeal T₀
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (hf N).comp (Ideal.quotientMap _ (φ : T →+* T₀) hle)

private theorem abs_det {n : ℕ} {G G₀ O T T₀ : Type} [Group G] [TopologicalSpace G] [Group G₀] [TopologicalSpace G₀]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (p : G →* G₀) (hp : Continuous p) (D : W.GDet n T G) (D₀ : W.GDet n T₀ G₀)
    (hD : D.IsCont (maximalIdeal T)) (hD₀ : D₀.IsCont (maximalIdeal T₀)) {S : Set G} (hS : Dense S)
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom = D₀.chi (MonoidAlgebra.single (p g) 1)) :
    D.map φ.toRingHom = D₀.comap p := by
  have e : ∀ g, (D.map φ.toRingHom).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map φ.toRingHom :=
    fun g => by
      rw [← (AlgebraTools.Det.mapApi D _).1]
      simp
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  have h1 := congrFun (cu_ext _ hS (push_cont φ (hD i)) (fun N => (hD₀ i N).comp_continuous hp) fun g hg => by
    simp only [W.GDet.lam, ← h g hg, coeff_map, map_mul, map_pow, map_neg, map_one]
    rfl) g
  simp only [W.GDet.lam, map_mul, map_pow, map_neg, map_one] at h1
  simp only [W.GDet.lam, e, LvR.chi_comap, coeff_map]
  exact h1

private theorem abs_chr {n : ℕ} {Wl Dc O T T₀ k : Type} [Group Wl] [Group Dc] [TopologicalSpace Dc] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [CommRing O] [IsLocalRing O] [CommRing T] [Algebra O T] [Alg.IsCO O T] [CommRing T₀] [Algebra O T₀] [Alg.IsCO O T₀]
    (φ : T →ₐ[O] T₀) (inc : Wl →* Dc) (hd : DenseRange inc) (art : Wl →* kˣ) (ha : Function.Surjective art)
    (ψ : Fin n → Dc →* Tˣ) (ψ₀ : Fin n → Dc →* T₀ˣ) (c1 : ∀ i, Alg.AdicCont (maximalIdeal T) fun g => (ψ i g : T))
    (c0 : ∀ i, Alg.AdicCont (maximalIdeal T₀) fun g => (ψ₀ i g : T₀)) (ε : Dc → Tˣ) (ε₀ : Dc → T₀ˣ)
    (hε : ∀ g, φ (ε g) = ε₀ g) (u : Fin n → Uo k → T) (u₀ : Fin n → Uo k → T₀) (hu : ∀ i y, φ (u i y) = u₀ i y)
    (γ : Fin n → T) (γ₀ : Fin n → T₀) (hγ : ∀ i, φ (γ i) = γ₀ i)
    (a1 : ∀ i s (y : Uo k), art s = y → (ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) * u i y = 1)
    (a0 : ∀ i s (y : Uo k), art s = y → (ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) * u₀ i y = 1)
    (b1 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ i (inc s) * ε (inc s) ^ (i : ℕ) : Tˣ) : T) = γ j)
    (b0 : ∀ j s, art s = Hi.unif k → ((∏ i with i ≤ j, ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ) : T₀ˣ) : T₀) = γ₀ j) (i : Fin n) :
    W.pushCh φ.toRingHom (ψ i) = ψ₀ i := by
  have hm : ∀ i g, φ ((ψ i g * ε g ^ (i : ℕ) : Tˣ) : T) = ((W.pushCh φ.toRingHom (ψ i) g * ε₀ g ^ (i : ℕ) : T₀ˣ) : T₀) :=
    fun i g => by
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hε]
      rfl
  refine MonoidHom.ext fun g => Units.ext (congrFun (cu_ext _ hd (push_cont φ (c1 i)) (c0 i) ?_) g)
  rintro _ ⟨s, rfl⟩
  refine congrArg Units.val (cu_gen art ha ((W.pushCh φ.toRingHom (ψ i)).comp inc) ((ψ₀ i).comp inc)
    (fun s y hy => ?_) (fun s hs => ?_) s)
  · have e := congrArg φ (a1 i s y hy)
    rw [map_mul, hm, hu, map_one] at e
    have e' := a0 i s y hy
    exact mul_right_cancel (inv_injective (Units.ext
      ((Units.eq_inv_of_mul_eq_one_left e).symm.trans (Units.eq_inv_of_mul_eq_one_left e'))))
  · refine mul_right_cancel (cu_prod (fun i => W.pushCh φ.toRingHom (ψ i) (inc s) * ε₀ (inc s) ^ (i : ℕ))
      (fun i => ψ₀ i (inc s) * ε₀ (inc s) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have e := congrArg φ (b1 j s hs)
    rw [Units.coe_prod, map_prod, hγ] at e
    rw [b0 j s hs, ← e, Units.coe_prod]
    exact Finset.prod_congr rfl fun i _ => (hm i _).symm

private theorem heckePol_map' {T T₀ : Type} [CommRing T] [CommRing T₀] (f : T →+* T₀) (n q : ℕ) (g : ℕ → T) :
    (heckePol n q g).map f = heckePol n q fun j => f (g j) := JEx.heckePol_map _ _ _ _

set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.levelUR2BaseEq :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : (hset Q₀ τ₀).X.I.T →* Aˣ), (hset Q₀ τ₀).IsWt θ → ∀ (a : (hset Q₀ τ₀).Op → c.O) (K₀ : (hset Q₀ τ₀).Lev) (K : (hset Q τ₀).Lev), ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q τ₀).Op → (hset Q₀ τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → ∀ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O), (hset Q τ₀).IsWt θ' → @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ → (∀ i, a' i = a (j i)) → ∀ [Fact (CommOn ((hset Q₀ τ₀).MK θ a K₀) ((hset Q₀ τ₀).op A))] [Alg.IsCO c.O ((hset Q₀ τ₀).TK θ a K₀)] [Fact (CommOn ((hset Q τ₀).MK θ' a' K) ((hset Q τ₀).op A))] [Alg.IsCO c.O ((hset Q τ₀).TK θ' a' K)] (D₀ : W.GDet n ((hset Q₀ τ₀).TK θ a K₀) V₀.frame.G₀) (ψ₀ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q₀ τ₀).TK θ a K₀)ˣ), (hset Q₀ τ₀).IsUniv θ a K₀ (maximalIdeal _) D₀ ψ₀ → ∀ (D : W.GDet n ((hset Q τ₀).TK θ' a' K) V.frame.G₀) (ψ : ∀ v : Vl l L, Fin n → Dec (F := L) (s.A v.1) →* ((hset Q τ₀).TK θ' a' K)ˣ), (hset Q τ₀).IsUniv θ' a' K (maximalIdeal _) D ψ → ∀ φ : (hset Q τ₀).TK θ' a' K →ₐ[A] (hset Q₀ τ₀).TK θ a K₀, (∀ i, φ ((hset Q τ₀).gen θ' a' K i) = (hset Q₀ τ₀).gen θ a K₀ (j i)) → D.map φ.toRingHom = D₀.comap p ∧ ∀ v i, W.pushCh φ.toRingHom (ψ v i) = ψ₀ v i := by
  intro hN l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c m τ₀ A _ _ _ θ _ a K₀ K p hp _ hpr j hj hjw θ' a' _ hθ _ _ _ _ _ D₀ ψ₀ hU₀ D ψ hU φ hφ
  have hAx := axU hN l L Ω s n hn V Q c m τ₀
  refine ⟨abs_det (φ.restrictScalars c.O) p hp D D₀ hU.cont hU₀.cont hAx.dense ?_, fun v i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    obtain ⟨hw₀, -⟩ := hjw ⟨w, hw⟩ ⟨0, hn⟩
    have e1 := hU.frob ⟨w, hw⟩ B σ hB hσ
    have e0 := hU₀.frob ⟨w, hw₀⟩ B σ hB hσ
    refine ((congrArg (Polynomial.map _) e1).trans ((heckePol_map' _ _ _ _).trans ?_)).trans
      (e0.symm.trans (congrArg (fun g => D₀.chi (MonoidAlgebra.single g 1)) (hpr σ⁻¹).symm))
    refine congrArg (heckePol n (normV w)) (funext fun k => ?_)
    unfold HSet.genW
    split_ifs with h
    · obtain ⟨_, e⟩ := hjw ⟨w, hw⟩ ⟨k - 1, h.2⟩
      exact (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) e)
    · exact map_one _
  · exact abs_chr (k := ((hset Q τ₀).Sl v).adicCompletion L) (φ.restrictScalars c.O) (Subgroup.inclusion (Weil_le_Dec (s.hw v.1))) (UpperTheory.weil_group_dense_in_galois_group L Ω _ _ (s.hw v.1))
      ((hset Q τ₀).art v) (hAx.art_spec v).surj (ψ v) (ψ₀ v) (hU.ψ_cont v) (hU₀.ψ_cont v)
      ((hset Q τ₀).epsV _ v) ((hset Q₀ τ₀).epsV _ v) (fun g => (φ.restrictScalars c.O).commutes _)
      (fun i y => algebraMap A _ (θ' (eV n (hset Q τ₀).Sl v i y))) (fun i y => algebraMap A _ (θ (eV n (hset Q₀ τ₀).Sl v i y)))
      (fun i y => (φ.commutes _).trans (congrArg (fun u : Aˣ => algebraMap A _ (u : A))
        (congrArg (fun t : (hset Q τ₀).X.I.T →* Aˣ => t (eV n (hset Q τ₀).Sl v i y)) hθ)))
      _ _ (fun k => (hφ _).trans (congrArg ((hset Q₀ τ₀).gen θ a K₀) (hj (v, k))))
      (fun i x y h => hU.ψ_unit v i x _ y rfl h) (fun i x y h => hU₀.ψ_unit v i x _ y rfl h)
      (fun k x h => hU.ψ_unif v k x _ rfl h) (fun k x h => hU₀.ψ_unif v k x _ rfl h) i
end
