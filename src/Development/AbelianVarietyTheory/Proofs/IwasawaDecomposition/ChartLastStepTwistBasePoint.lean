module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanning
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValLtOfRedM
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertHeckeOperatorIndepOfInertDatum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartFromAdelicDictionary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinates
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

open GlobalTheory.Mem.Col2

theorem stpTop_groupClasses : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  have hne : B.R.m + 1 ≠ B.R.m := by omega
  have hY : ∀ p : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.2 = ∅ := by
    intro p
    have h := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hne] at h
    exact h
  have hpt : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, p.1.1 = q.1.1 → p = q := by
    intro p q h
    exact Subtype.ext (Prod.ext h ((hY p).trans (hY q).symm))
  have hcos : ∀ p q : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m, cosetIn p = cosetIn q := by
    intro p q
    funext P
    ext z
    simp [cosetIn, hY p, hY q]
  set S := I.stp u a B.R.m with hS
  have key : ∀ (T : GStep B.fields.E B.fields.K (B.R.N B.R.m)) (b : T.β) (x y : T.D b) (g : T.G b), g • x = y →
      (Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) x) = Quotient.mk (MulAction.orbitRel (T.G b) (T.D b)) y :=
    fun T b x y g h => Quotient.sound ⟨g⁻¹, by rw [← h]; exact inv_smul_smul g x⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨_ | al, hb⟩, q⟩
    · refine ⟨Equiv.refl _, fun κ => ⟨rfl, rfl, rfl, rfl, hcos _ _, fun h => hpt _ _ h⟩⟩
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · rintro ⟨⟨_ | al, hb⟩, q⟩ ⟨⟨_ | al', hb'⟩, q'⟩ γ h θ hγ
    · have e1 : S.act ⟨none, hb⟩ (γ, h, θ) (S.rep ⟨⟨none, hb⟩, q⟩) = S.rep ⟨⟨none, hb'⟩, q'⟩ := hpt _ _ hγ
      have hq : q = q' := by
        have h1 := S.rp_spec ⟨none, hb⟩ q
        have h2 := S.rp_spec ⟨none, hb'⟩ q'
        rw [← h1, ← h2]
        exact key S _ _ _ _ e1
      subst hq
      rfl
    · exact absurd (hb'.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
    · exact absurd (hb.1 rfl) (lt_irrefl _)
  · intro p
    obtain ⟨pt, hpt'⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m) p
    let b : S.β := Idx.top I.sel (I.tup a) (I.idx a) le_rfl
    obtain ⟨g, hg⟩ := S.exists_mv b pt
    refine ⟨S.cl b pt, g.1, g.2.1, g.2.2, ?_⟩
    exact (congrArg (fun x : PtAt (Pr := B.primes X) B.R I.sel (I.tup a) (I.cst a) u B.R.m => x.1.1) hg).trans hpt'
  · haveI : NeZero (B.R.N B.R.m) := ⟨by have := N_m_succ B.R; omega⟩
    obtain ⟨pt, -⟩ := exists_ptAt I.sel (I.tup a) (I.cst a) (R := B.R) (u := u) (j := B.R.m)
      (DecoF.base _ _ _ _ _)
    exact ⟨S.cl (Idx.top I.sel (I.tup a) (I.idx a) le_rfl) pt⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastStepTupleGroupClassesCoordinatesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_tuple_group_classes_coordinates : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι), (∀ c : (I.stp u a B.R.m).Cl, ∃ e : (I.stp u a B.R.m).G c.1 ≃ (UF B.host.E (B.R.N B.R.m) × ((I.Tp a).levG B.R.m).grp × ((I.Tp a).levQ B.R.m).grp), ∀ κ : (I.stp u a B.R.m).G c.1, (e κ).1 = κ.1 ∧ (I.stp u a B.R.m).gam c.1 κ = ufGL B.host.E (B.R.N B.R.m) (e κ).1 ∧ (I.stp u a B.R.m).chr c.1 κ = ((I.Tp a).levG B.R.m).chr (e κ).2.1 * ((I.Tp a).levQ B.R.m).chr (e κ).2.2 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = (((e κ).1, (e κ).2.1.1, (e κ).2.2.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 ∧ cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) ∧ (((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = ((I.stp u a B.R.m).rep c).1.1 → (I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c) = (I.stp u a B.R.m).rep c)) ∧ (∀ (c c' : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).rep c').1.1 → c = c') ∧ (∀ p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a), ∃ (c : (I.stp u a B.R.m).Cl) (γ : UF B.host.E (B.R.N B.R.m)) (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp), ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c).1.1 = p) ∧ Nonempty (I.stp u a B.R.m).Cl := by
  intro B X I u a
  exact GlobalTheory.stpTop_groupClasses I u a
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePoint
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.TopCh

theorem latS_mul_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {Lb L L' S : Submodule (𝓞 E) (Fin n → E)} {y y' k : GL (Fin n) (AfE F E)}
    (hyl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L ↔ (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb)
    (hL : L = L') (hy : y = y')
    (hl : ∀ w : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) L' ↔ ((y' * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S)
    (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Lb ↔ (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) S := by
  subst hL hy
  have e1 : (y⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have e2 : ((y * k)⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ (y.1 *ᵥ x) = (k⁻¹ : GL (Fin n) (AfE F E)).1 *ᵥ x := by
    have e : (y * k)⁻¹ * y = k⁻¹ := by group
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, e]
  have h1 := hyl (y.1 *ᵥ x)
  have h2 := hl (y.1 *ᵥ x)
  rw [e1] at h1
  rw [e2] at h2
  exact h1.symm.trans h2


set_option maxHeartbeats 2000000 in
theorem kread_member : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  intro B X I hI hP l Z u a K k hR U Lb chi
  have hQ0 : I.Q I.mu0 = ∅ := ColIn.twistPrimes_reference_tuple_eq_empty I
  have hG : (I.Tp a).levG B.R.m = (I.Tp I.mu0).levG B.R.m := by
    rw [TC.Tp, TC.Tp, topLev_levG_m, topLev_levG_m]
  obtain ⟨c₀⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u I.mu0).1 c₀
  have hp := (hR.pt c₀).of_extTo (I.Q_subset_SQ I.mu0) (by rw [hQ0]; exact Finset.disjoint_empty_right _)
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : GA B (B.R.N B.R.m), y₀ = (K.y c₀).1 := ⟨_, rfl⟩
  rw [← hy₀] at hp
  rw [hG]

  have hθ : ∀ θ : ((I.Tp I.mu0).levQ B.R.m).grp, θ = 1 := fun θ =>
    Subtype.ext (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim)

  have hD : ∀ q q' : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0), q.deco = q'.deco → q = q' :=
    fun q q' h => Subtype.ext (Prod.ext h (funext fun P => (Finset.notMem_empty P.1 (hQ0 ▸ P.2)).elim))
  have hgam : ∀ γ : UF B.host.E (B.R.N B.R.m), ufGL B.host.E (B.R.N B.R.m) γ = 1 → γ = 1 := fun γ h =>
    Subtype.ext ((toGLm B.host.E (B.R.N B.R.m)).injective (by show _ = toGLm B.host.E (B.R.N B.R.m) 1; rw [map_one]; exact h))
  have hmul : ∀ x : GA B (B.R.N B.R.m), y₀ * k () * ((k ())⁻¹ * x * k ()) = y₀ * x * k () := fun x => by group
  have hku : k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    obtain ⟨p₀, hp₀, -⟩ := hR.k_std ()
    exact hp₀.uni
  have hyu : y₀ ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    have := mul_mem hp.uni (inv_mem hku)
    rwa [mul_inv_cancel_right] at this

  have hact : ∀ h : ((I.Tp I.mu0).levG B.R.m).grp,
      (I.stp u I.mu0 B.R.m).gam c₀.1 (e.symm (1, h, 1)) = 1 ∧
      ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)).1.1 =
        ((1 : UF B.host.E (B.R.N B.R.m)), h.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ∧
      cosetIn ((I.stp u I.mu0 B.R.m).act c₀.1 (e.symm (1, h, 1)) ((I.stp u I.mu0 B.R.m).rep c₀)) =
        cosetIn ((I.stp u I.mu0 B.R.m).rep c₀) ∧
      (I.stp u I.mu0 B.R.m).chr c₀.1 (e.symm (1, h, 1)) = ((I.Tp I.mu0).levG B.R.m).chr h := fun h => by
    obtain ⟨-, h1, h2, h3, h4, -⟩ := he (e.symm (1, h, 1))
    rw [e.apply_symm_apply] at h1 h2 h3
    refine ⟨by rw [h1]; exact map_one _, by rw [h3]; rfl, h4, by rw [h2, map_one, mul_one]⟩
  refine ⟨fun x hxu => ?_, fun x z h hz hred => ?_, fun x => ?_⟩
  · have hgu : y₀ * x * k () ∈ UAd B.sp.cm (B.R.N B.R.m) := mul_mem (mul_mem hyu hxu) hku
    obtain ⟨q, hq⟩ := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * x * k ()) 1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 1).2.2 hQ0 hgu
    have H2 := fun h => (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 q h).1 hp (by rw [hmul]; exact hq)
    have hq' := hq
    rw [hy₀] at hq'
    rw [hR.lev c₀ x q hq', levU, Subgroup.mem_map]
    constructor
    · rintro ⟨κ, hκ1, hκq, -⟩
      obtain ⟨-, hg, -, h3, -⟩ := he κ
      have e1 : (e κ).1 = 1 := hgam _ (by rw [← hg]; exact hκ1)
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (e κ).2.1.1, (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) •
          ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by
        rw [← hκq, h3, e1, hθ (e κ).2.2]; rfl
      obtain ⟨hz, hred⟩ := (H2 (e κ).2.1.1).2 (by rw [hq2]; rfl)
      exact ⟨⟨_, hz⟩, by show redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz⟩ ∈ ((I.Tp I.mu0).levG B.R.m).grp; rw [hred]; exact inv_mem (e κ).2.1.2, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have hz : (k ())⁻¹ * x * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hwz ▸ w.2
      have hw' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w ∈ ((I.Tp I.mu0).levG B.R.m).grp := hw
      have hd := (H2 (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹).1
        ⟨hz, by rw [inv_inv]; congr 1; exact Subtype.ext hwz.symm⟩
      have hq2 : q = ((1 : UF B.host.E (B.R.N B.R.m)), (redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs w)⁻¹,
          (1 : GLQ B.host.E (B.R.N B.R.m) (I.Q I.mu0))) • ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := hD _ _ hd
      obtain ⟨g1, g2, g3, -⟩ := hact ⟨_, inv_mem hw'⟩
      refine ⟨e.symm (1, ⟨_, inv_mem hw'⟩, 1), g1, ?_, g3⟩
      rw [g2, hq2]
  · have hz' : (k ())⁻¹ * x.1 * k () ∈ J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) := hz ▸ z.2
    have hred' : redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ⟨_, hz'⟩ = h.1⁻¹ := by
      rw [← hred]; congr 1; exact Subtype.ext hz.symm
    have hpt := (GlobalTheory.T.isPtOf_mul_J0_decoration B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (y₀ * k ()) ((k ())⁻¹ * x.1 * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 ((I.stp u I.mu0 B.R.m).rep c₀).1.1 h.1).2.1 hQ0 hp hz' hred'
    rw [hmul] at hpt
    obtain ⟨g1, g2, -, g4⟩ := hact h
    have := hR.chr c₀ x (e.symm (1, h, 1)) g1 (by rw [g2, ← hy₀]; exact hpt)
    rw [g4] at this
    exact Units.ext this
  · have hS : ∀ w : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F,
        w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) ↔
        ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) :=
      fun w => by
        have e : ((1 : GA B (B.R.N B.R.m))⁻¹ : GA B (B.R.N B.R.m)).1 *ᵥ w = w := by rw [inv_one, Units.val_one, Matrix.one_mulVec]
        rw [e]
    have hp1 : IsPtOf B.sp.cm (y₀ * k () * (1 * 1)) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 := by rw [mul_one, mul_one]; exact hp
    have hl := GlobalTheory.T.pointLattice_iff_baseLattice_decorated B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q I.mu0)
      (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) 1 1 (y₀ * k ()) ((I.stp u I.mu0 B.R.m).rep c₀).1.1 (one_mem _) hS hp1
    have hc := (((spaces_in_coordinates I hI hP l Z).2.2.2 B.R.m le_rfl).2.2 u I.mu0).1 c₀
    exact latS_mul_iff (K.y_lat c₀) hc hy₀.symm hl x

end GlobalTheory.Mem.Col2.TopCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnMemberLevelReadAtBasePointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumn_member_level_read_at_base_point : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → Pins B X → ∀ (l : I.Laws) (Z : Later B (I.cols l)) (u : B.Word) (a : I.ι) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl) (k : Unit → GA B (B.R.N B.R.m)), I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k → let U : Subgroup (GA B (B.R.N B.R.m)) := K.lev.U; let Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E) := K.lev.Lb; let chi : U →* ℂˣ := K.lev.chi; (∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U ↔ (k ())⁻¹ * x * k () ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp) ∧ (∀ (x : U) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = (k ())⁻¹ * x.1 * k () → redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h)) ∧ ∀ x : Fin (B.R.N B.R.m) → B.host.E ⊗[B.host.F] FiniteAdeleRing (𝓞 B.host.F) B.host.F, x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) Lb ↔ ((k ())⁻¹ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)).1 *ᵥ x ∈ latS (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (tensInt (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F) (intOE B.host.E) (intAd B.host.F)) (baseLb B.host.E (B.R.N B.R.m) ((B.primes X).vT u)) := by
  first | exact @GlobalTheory.Mem.Col2.TopCh.kread_member | exact GlobalTheory.Mem.Col2.TopCh.kread_member | (intros; apply GlobalTheory.Mem.Col2.TopCh.kread_member <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePoint
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TwTop

section Rho

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem localComponent_congr (P : HeightOneSpectrum (𝓞 E)) {v : HeightOneSpectrum (𝓞 F)} (hv : P.under (𝓞 F) = v) {x x' : GL (Fin n) (AfE F E)}
    (h : bc (prV (E := E) v) x = bc (prV (E := E) v) x') : rhoP F P x = rhoP F P x' := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : prV (E := E) v (x.1 i j - x'.1 i j) = 0 := by
    have := congrArg (fun g : GL (Fin n) _ => g.1 i j) h
    rw [map_sub, sub_eq_zero]
    exact this
  have h2 := ((GlobalTheory.T.placeProjection_zero_integral_iff_components_above F E v _).1.1 h1) P hv
  rw [map_sub, sub_eq_zero] at h2
  exact h2

theorem bc_prV_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : GL (Fin n) (AfE F E)}
    (h : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ i j : Fin n, adAt F w (x.1 i j) = if i = j then 1 else 0) :
    bc (prV (E := E) v) x = 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h1 : prV (E := E) v (x.1 i j - (1 : Matrix (Fin n) (Fin n) (AfE F E)) i j) = 0 := by
    refine (GlobalTheory.T.placeProjection_zero_integral_iff_components_above F E v _).1.2 fun w hw => ?_
    rw [map_sub, h w hw, Matrix.one_apply]
    split_ifs <;> simp
  rw [map_sub, sub_eq_zero] at h1
  refine h1.trans ?_
  show _ = (1 : Matrix (Fin n) (Fin n) _) i j
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem localComponent_mul_inv_entry (P : HeightOneSpectrum (𝓞 E)) (k t : GL (Fin n) (AfE F E)) (ht : rhoP F P t = 1) (r j : Fin n) :
    adAt F P (((k * t)⁻¹ : GL (Fin n) (AfE F E)).1 r j) = adAt F P (((k)⁻¹ : GL (Fin n) (AfE F E)).1 r j) := by
  have e : rhoP F P (k * t)⁻¹ = rhoP F P k⁻¹ := by
    rw [_root_.mul_inv_rev, map_mul, map_inv (rhoP F P) t, ht, inv_one, one_mul]
  exact congrArg (fun g : GL (Fin n) (P.adicCompletion E) => g.1 r j) e

theorem localComponent_eq_one (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) (h : ∀ i j : Fin n, adAt F P (t.1 i j) = if i = j then 1 else 0) :
    rhoP F P t = 1 := by
  refine Units.ext (Matrix.ext fun i j => (h i j).trans ?_)
  show _ = (1 : Matrix _ _ _) i j
  rw [Matrix.one_apply]

end Rho

section Chi

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]

theorem topChi_facts (_hc : CMData F E) (n : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 E))) (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E)))
    (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0) (N : Q → ℕ)
    (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) :
    ((∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ g, (Θ P).lam g ^ m = 1) → ∃ m : ℕ, 0 < m ∧ ∀ x, topChi σ U t Θ d hd N hdN hΘ x ^ m = 1) ∧
      ∀ x : topU U t Θ d, (∀ P : Q, rhoP F P.1 x.1 = 1) → topChi σ U t Θ d hd N hdN hΘ x = 1 :=
  GlobalTheory.T.levelCharacterAtQ_finite_order_and_trivial F E K n Q σ U t Θ d hd N hdN hΘ

end Chi

end GlobalTheory.Mem.Col2.TwTop

namespace GlobalTheory.Mem.Col2.TC

open TopCh TwTop Formalism.L2.Herm

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem cosetIn_top (u : B.Word) (a : I.ι) (c : (I.stp u a B.R.m).Cl) : cosetIn ((I.stp u a B.R.m).rep c) = fun _ => ∅ := by
  have h : ((I.stp u a B.R.m).rep c).1.2 = ∅ := by
    have h1 := ((I.stp u a B.R.m).rep c).2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) (by omega)] at h1
    exact h1
  funext P
  ext z
  simp [cosetIn, h]

theorem idx_top (u : B.Word) (a : I.ι) (b b' : (I.stp u a B.R.m).β) : b = b' :=
  (Idx.eq_top b le_rfl).trans (Idx.eq_top b' le_rfl).symm

abbrev dTop (a : I.ι) : I.Q a → B.host.E := fun P => ((qOf P.1 : ℕ) : B.host.E) ^ (topDep B.R (I.cst a).M + 1)

theorem dTop_ne (a : I.ι) (P : I.Q a) : I.dTop a P ≠ 0 := pow_ne_zero _ GlobalTheory.TopStep.qOf_ne_zero

section Top

variable (u : B.Word) (a : I.ι) (N : I.Q a → ℕ) (hdN : ∀ P : I.Q a, P.1.valuation B.host.E (I.dTop a P) ≤ WithZero.exp (-(N P : ℤ)))
  (hΘ : ∀ (P : I.Q a) (g : ↥(GLint B.host.E (B.R.N B.R.m) P.1)), lqPrinc P.1 (N P) (g : Sp B.host.E (B.R.N B.R.m) ≃ₗ[B.host.E] Sp B.host.E (B.R.N B.R.m)) →
      ∃ h : g ∈ ((I.Tp a).levQ B.R.m P).H, ((I.Tp a).levQ B.R.m P).lam ⟨g, h⟩ = 1)
  (U0 : Subgroup (GA B (B.R.N B.R.m))) (chi0 : U0 →* ℂˣ) (k t : GA B (B.R.N B.R.m))
  (hkU : k ∈ UAd B.sp.cm (B.R.N B.R.m)) (hkQ : ∀ P : I.Q a, rhoP B.host.F P.1 k = 1)
  (ht : t ∈ K1 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs)
  (hU : ∀ x ∈ UAd B.sp.cm (B.R.N B.R.m), x ∈ U0 ↔ k⁻¹ * x * k ∈ levU B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs ((I.Tp a).levG B.R.m).grp)
  (hχ : ∀ (x : U0) (z : J0 B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u)) (h : ((I.Tp a).levG B.R.m).grp), z.1 = k⁻¹ * x.1 * k →
      redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z = h.1⁻¹ → chi0 x = Units.map (B.embLL : B.LL →* ℂ) (((I.Tp a).levG B.R.m).chr h))


include hdN hΘ hkU hkQ ht hU in
theorem lev_top (c : (I.stp u a B.R.m).Cl) (y x : GA B (B.R.N B.R.m)) (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m)
    (h1 : PtOf (y * (k * t)) ((I.stp u a B.R.m).rep c).1.1) (h2 : PtOf (y * x * (k * t)) q) :
    x ∈ topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) ↔ ∃ κ : (I.stp u a B.R.m).G c.1, (I.stp u a B.R.m).gam c.1 κ = 1 ∧ ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1 = q ∧
      cosetIn ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) := by
  have core := GlobalTheory.T.mem_framedLevel_iff_two_adelic_points B.host.F B.host.E B.LL B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) ((I.Tp a).levG B.R.m) ((I.Tp a).levQ B.R.m)
    (I.dTop a) (I.dTop_ne a) N hdN hΘ U0 k t y x _ q hkU hkQ ht hU h1 h2
  obtain ⟨e, he⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u a).1 c
  rw [core]
  constructor
  · rintro ⟨h, θ, hh⟩
    obtain ⟨-, e2, -, e4, e5, -⟩ := he (e.symm (1, h, θ))
    simp only [Equiv.apply_symm_apply] at e2 e4
    exact ⟨e.symm (1, h, θ), e2.trans (map_one _), e4.trans hh, e5⟩
  · rintro ⟨κ, g1, g2, -⟩
    obtain ⟨-, e2, -, e4, -, -⟩ := he κ
    have hγ : (e κ).1 = 1 := Subtype.ext ((toGLm B.host.E (B.R.N B.R.m)).injective ((e2.symm.trans g1).trans (map_one (toGLm B.host.E (B.R.N B.R.m)).toMonoidHom).symm))
    refine ⟨(e κ).2.1, (e κ).2.2, ?_⟩
    rw [← g2, e4, hγ]


include hkU hkQ ht hχ in
theorem chr_top (c : (I.stp u a B.R.m).Cl) (y : GA B (B.R.N B.R.m)) (x : topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a)) (κ : (I.stp u a B.R.m).G c.1)
    (h1 : PtOf (y * (k * t)) ((I.stp u a B.R.m).rep c).1.1) (g1 : (I.stp u a B.R.m).gam c.1 κ = 1)
    (g2 : PtOf (y * x.1 * (k * t)) ((I.stp u a B.R.m).act c.1 κ ((I.stp u a B.R.m).rep c)).1.1) :
    chi0 ⟨x.1, topU_le _ _ _ _ x.2⟩ * topChi B.embLL U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) (I.dTop_ne a) N hdN hΘ x = Units.map (B.embLL : B.LL →* ℂ) ((I.stp u a B.R.m).chr c.1 κ) := by
  obtain ⟨e, he⟩ := (GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u a).1 c
  obtain ⟨-, e2, e3, e4, -, -⟩ := he κ
  have hγ : (e κ).1 = 1 := Subtype.ext ((toGLm B.host.E (B.R.N B.R.m)).injective ((e2.symm.trans g1).trans (map_one (toGLm B.host.E (B.R.N B.R.m)).toMonoidHom).symm))
  rw [e4, hγ] at g2
  rw [e3]
  exact GlobalTheory.T.levelFrameCharacter_mul_movedPoint B.host.F B.host.E B.LL B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) ((I.Tp a).levG B.R.m) ((I.Tp a).levQ B.R.m)
    (I.dTop a) (I.dTop_ne a) N hdN hΘ B.embLL U0 chi0 k t y _ hkU hkQ ht hχ x (e κ).2.1 (e κ).2.2 h1 g2


include hdN hΘ hkU hkQ ht hU hχ in
theorem reads_top (Lbc : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) (Uc : Subgroup (GA B (B.R.N B.R.m))) (chi : Uc →* ℂˣ)
    (yc : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)) (st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E)
    (hlb : ∀ x, x ∈ Lbc ↔ x ∈ baseL B (B.R.N B.R.m) (X.piT u))
    (hstd : ∃ p : DecoF B.fields.E (B.R.N B.R.m) ∅ ∅ ∅, PtOf (k * t) p ∧ p.deco.1.N = stdLat B.fields.E (B.R.N B.R.m))
    (hoff : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (k * t) = 1)
    (hT : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 (((k * t)⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0))
    (hpt : ∀ c, PtOf (yc c * (k * t)) (extTo I.SQ ((I.stp u a B.R.m).rep c).1.1)) (hpt' : ∀ c, PtOf (yc c * (k * t)) ((I.stp u a B.R.m).rep c).1.1)
    (hUc : Uc = topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a))
    (hchi : ∀ (x : Uc) (x' : U0) (x'' : topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a)), x.1 = x'.1 → x.1 = x''.1 →
      chi x = chi0 x' * topChi B.embLL U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) (I.dTop_ne a) N hdN hΘ x'')
    (hst : ∀ c s, st c s = (I.stp u a B.R.m).gam c.1 s.1) :
    I.Reads u a B.R.m (fun _ => ()) (fun _ => Lbc) (fun _ => Uc) (fun _ => chi) yc st (fun _ => k * t) := by
  obtain ⟨-, -, -, hne⟩ := GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u a
  refine { key := fun c c' => ⟨fun _ => ⟨idx_top I u a _ _, by rw [cosetIn_top, cosetIn_top]⟩, fun _ => rfl⟩
           onto := fun _ => ⟨hne.some, rfl⟩
           lb := fun _ x => hlb x
           k_std := fun _ => hstd
           k_off := fun _ v h1 h2 _ => hoff v h1 h2
           k_T := fun _ => hT
           pt := hpt
           lev := fun c x q hq => ?_
           chr := fun c x κ g1 g2 => ?_
           stab := hst }
  · show x ∈ Uc ↔ _
    rw [hUc]
    exact lev_top I u a N hdN hΘ U0 k t hkU hkQ ht hU c (yc c) x q (hpt' c) hq
  · have hx : x.1 ∈ topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) := hUc ▸ x.2
    have e := chr_top I u a N hdN hΘ U0 chi0 k t hkU hkQ ht hχ c (yc c) ⟨x.1, hx⟩ κ (hpt' c) g1 g2
    have e' := hchi x ⟨x.1, topU_le _ _ _ _ hx⟩ ⟨x.1, hx⟩ rfl rfl
    show ((chi x : ℂˣ) : ℂ) = _
    rw [e', e]
    rfl


include hχ hU in
theorem root_top (hle : U0 ≤ UAd B.sp.cm (B.R.N B.R.m)) (Uc : Subgroup (GA B (B.R.N B.R.m))) (chi : Uc →* ℂˣ)
    (hUc : Uc = topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a))
    (hchi : ∀ (x : Uc) (x' : U0) (x'' : topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a)), x.1 = x'.1 → x.1 = x''.1 →
      chi x = chi0 x' * topChi B.embLL U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) (I.dTop_ne a) N hdN hΘ x'') :
    ∃ n : ℕ, 0 < n ∧ ∀ κ, chi κ ^ n = 1 := by
  obtain ⟨m1, hm1, e1⟩ := GlobalTheory.T.exists_levelFamily_character_exponent ((I.Tp a).levG B.R.m)
  obtain ⟨m2, hm2, e2⟩ := (topChi_facts B.sp.cm (B.R.N B.R.m) (I.Q a) B.embLL U0 t ((I.Tp a).levQ B.R.m) _ (I.dTop_ne a) N hdN hΘ).1
    (fun P => topLevAt_root I.Ch I.sel (I.tup a) I.Ps _ B.R.m P)
  refine ⟨m1 * m2, Nat.mul_pos hm1 hm2, fun κ => ?_⟩
  have hx : κ.1 ∈ topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) := hUc ▸ κ.2
  have hx0 : κ.1 ∈ U0 := topU_le _ _ _ _ hx
  obtain ⟨z, hz, hze⟩ := (hU _ (hle hx0)).1 hx0
  have hc := hχ ⟨κ.1, hx0⟩ z ⟨(redG B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs z)⁻¹, inv_mem hz⟩ hze (by simp)
  rw [hchi κ ⟨κ.1, hx0⟩ ⟨κ.1, hx⟩ rfl rfl, hc, mul_pow, ← map_pow, pow_mul, e1, one_pow, map_one, one_mul, mul_comm m1 m2, pow_mul, e2, one_pow]


include hdN hΘ hkU hkQ ht hU in
theorem top_base (p : DecoF B.host.E (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a)) (y g : GA B (B.R.N B.R.m))
    (h1 : PtOf (g * (k * t)) p) (h2 : PtOf (y * (k * t)) p) : g⁻¹ * y ∈ topU U0 t ((I.Tp a).levQ B.R.m) (I.dTop a) := by
  have h3 : PtOf (g * (g⁻¹ * y) * (k * t)) p := by rwa [mul_inv_cancel_left]
  refine (GlobalTheory.T.mem_framedLevel_iff_two_adelic_points B.host.F B.host.E B.LL B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) ((I.Tp a).levG B.R.m) ((I.Tp a).levQ B.R.m)
    (I.dTop a) (I.dTop_ne a) N hdN hΘ U0 k t g _ p p hkU hkQ ht hU h1 h3).2 ⟨1, 1, ?_⟩
  exact one_smul _ _

end Top


set_option maxHeartbeats 16000000 in
theorem chart_twm : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ (K1 : ∀ β : Unit, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) B.R.m le_rfl (fun c : {c // (fun _ : (I.stp u a B.R.m).Cl => ()) c = β} => (I.chain l u a).stab B.R.m c.1) (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))), (∃ k, I.Reads u a B.R.m (fun _ => ()) (fun β => (K1 β).lev.Lb) (fun β => (K1 β).lev.U) (fun β => (K1 β).lev.chi) (fun c => ((K1 ()).y ⟨c, rfl⟩).1) (fun c s => ((K1 ()).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * k β) (tilF I.sel (I.tup a) u d)) ∧ I.TopBase l Z u a (K1 ()).lev.U (fun c => ((K1 ()).y ⟨c, rfl⟩).1) ∧ (∀ v, v ∉ Q → (K1 ()).lev.Uloc v = K.lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K1 ()).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K1 ()).lev.U) (κ' : K.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K1 ()).lev.chi κ = K.lev.chi κ' := by
  intro B X I hOk hPins l Z u a Q K hQ hk
  obtain ⟨k, hk⟩ := hk
  classical
  obtain ⟨hQ0, hf'⟩ := GlobalTheory.T.twistPrimes_away_level_and_type_primes I hOk
  have hf := hf' u a
  obtain ⟨hU, hχ, hLb⟩ := GlobalTheory.T.trueColumn_member_level_read_at_base_point I hOk hPins l Z u a K k hk
  have hgram := ((spaces_in_coordinates I hOk hPins l Z).2.2.2 B.R.m le_rfl).1
  have hcrd := (((spaces_in_coordinates I hOk hPins l Z).2.2.2 B.R.m le_rfl).2.2 u a).1
  obtain ⟨N, hdN, hΘ⟩ := GlobalTheory.T.lastStep_twist_level_contains_principal_congruence I a
  obtain ⟨t, ht, htP, htw⟩ := GlobalTheory.T.exists_unitaryAdelic_twist_diagonal_at_primes B.host.F B.host.E B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) (fun P hP => (hf P hP).1) (X.piT u)
    (fun P hP => (hf P hP).2.1)
  have hkstd := hk.k_std ()
  have hkU : k () ∈ UAd B.sp.cm (B.R.N B.R.m) := by
    obtain ⟨p, hp, -⟩ := hkstd
    exact hp.uni
  have hnoU : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [hQ0] at hP
    exact absurd hP (Finset.notMem_empty _)
  have hoff : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) (k ()) = 1 :=
    fun v hv => hk.k_off () v hv (hnoU v) (Or.inl rfl)
  have hkQ : ∀ P : I.Q a, rhoP B.host.F P.1 (k ()) = 1 := fun P => by
    have := TwTop.localComponent_congr (F := B.host.F) P.1 (v := P.1.under (𝓞 B.host.F)) rfl (x := k ()) (x' := 1) (by
      rw [hoff _ (hf P.1 P.2).2.2, map_one])
    rw [this, map_one]
  choose g hg using fun c : (I.stp u a B.R.m).Cl => GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists I hOk u (B.R.N B.R.m) (extTo I.SQ ((I.stp u a B.R.m).rep c).1.1)
  have hdisj : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_right.2 fun P hP => (hf P hP).1.2.1
  let y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m) := fun c => g c * (k () * t)⁻¹
  have hy : ∀ c, y c * (k () * t) = g c := fun c => inv_mul_cancel_right _ _
  have hpt : ∀ c, IsPtOf B.sp.cm (y c * (k () * t)) ((I.stp u a B.R.m).rep c).1.1 := fun c => by
    rw [hy]
    exact (hg c).of_extTo (I.Q_subset_SQ a) hdisj
  obtain ⟨hG, hcl1, hcl2, hcl3⟩ := GlobalTheory.T.lastStep_tuple_group_classes_coordinates I u a
  have hstepOk := (l.ch u a).step B.R.m
  let gm : ∀ c : {c : (I.stp u a B.R.m).Cl // (fun _ : (I.stp u a B.R.m).Cl => ()) c = ()}, (I.chain l u a).stab B.R.m c.1 →* UF B.host.E (B.R.N B.R.m) :=
    fun c => (MonoidHom.fst _ _).comp (Subgroup.subtype _)
  have hgm : ∀ c, Function.Injective (gm c) := fun c => (injective_iff_map_eq_one (gm c)).2 fun s hs => Subtype.ext
    (hstepOk.stab_inj c.1.1 s.1 ((I.stp u a B.R.m).rep c.1) s.2 (by
      show ufGL B.host.E (B.R.N B.R.m) (gm c s) = 1
      rw [hs, map_one]))
  have hgr : ∀ c (γ : UF B.host.E (B.R.N B.R.m)), γ ∈ (gm c).range ↔ ∃ (h : ((I.Tp a).levG B.R.m).grp) (θ : ((I.Tp a).levQ B.R.m).grp),
      ((γ, h.1, θ.1) : UF B.host.E (B.R.N B.R.m) × GLG (E := B.host.E) (n := B.R.N B.R.m) (SG := (B.primes X).vGs) × GLQ B.host.E (B.R.N B.R.m) (I.Q a)) • ((I.stp u a B.R.m).rep c.1).1.1 = ((I.stp u a B.R.m).rep c.1).1.1 := by
    intro c γ
    obtain ⟨e, he⟩ := hG c.1
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨e1, -, -, e4, -, -⟩ := he s.1
      have e5 : ((I.stp u a B.R.m).act c.1.1 s.1 ((I.stp u a B.R.m).rep c.1)).1.1 = ((I.stp u a B.R.m).rep c.1).1.1 :=
        congrArg (fun q => q.1.1) s.2
      have e6 : (e s.1).1 = gm c s := e1
      refine ⟨(e s.1).2.1, (e s.1).2.2, ?_⟩
      rw [← e6]
      exact e4.symm.trans e5
    · rintro ⟨h, θ, hh⟩
      obtain ⟨e1, -, -, e4, -, e6⟩ := he (e.symm (γ, h, θ))
      simp only [Equiv.apply_symm_apply] at e1 e4
      exact ⟨⟨e.symm (γ, h, θ), e6 (e4.trans hh)⟩, e1.symm⟩
  have hchiQ := topChi_facts B.sp.cm (B.R.N B.R.m) (I.Q a) B.embLL K.lev.U t ((I.Tp a).levQ B.R.m) _ (I.dTop_ne a) N hdN hΘ
  have hunder : ∀ P : HeightOneSpectrum (𝓞 B.host.E), (conjPrime₂ P).under (𝓞 B.host.F) = P.under (𝓞 B.host.F) := fun P =>
    (under_eq_iff B.host P _).2 (Or.inr rfl)
  obtain ⟨C, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_framed_chart_from_adelic_dictionary B.host.F B.host.E B.LL B.sp.cm (B.R.N B.R.m) ((B.primes X).vT u) (B.primes X).vGs (I.Q a) _ (B.T u) _ _ K.lev Q
    ((I.Tp a).levG B.R.m) ((I.Tp a).levQ B.R.m) (topDep B.R (I.cst a).M + 1) (I.dTop a) (I.dTop_ne a) N hdN hΘ (k ()) t
    {c : (I.stp u a B.R.m).Cl // (fun _ : (I.stp u a B.R.m).Cl => ()) c = ()} (fun c => ((I.stp u a B.R.m).rep c.1).1.1) (fun c => y c.1) _ _ gm
    (topChi B.embLL K.lev.U t ((I.Tp a).levQ B.R.m) (I.dTop a) (I.dTop_ne a) N hdN hΘ) hgram
    (fun v => (hQ v).trans Iff.rfl) (fun v hv => by
      obtain ⟨P, hP, rfl⟩ := (hQ v).1 hv
      exact (hf P hP).2.2) (fun P hP => (hf P hP).1) (fun _ => rfl) hkU hkQ ht hU hLb (fun c => hpt c.1)
    (fun c c' γ h θ e => Subtype.ext (hcl1 c.1 c'.1 γ h θ e))
    (fun p => by
      obtain ⟨c, γ, h, θ, e⟩ := hcl2 p
      exact ⟨⟨c, rfl⟩, γ, h, θ, e⟩)
    (fun c => (hcrd c.1)) hgm hgr (fun x hx => (hchiQ).2 x hx)
  have hkT := hk.k_T ()
  have hUle : (K.lev.U : Subgroup (GA B (B.R.N B.R.m))) ≤ UAd B.sp.cm (B.R.N B.R.m) := fun x hx => by
    have h0 := ((K.lev.U_eq x).1 hx).1
    rw [hgram] at h0
    exact h0
  have hy5 : ∀ c, (C.y ⟨c, rfl⟩).1 = y c := fun c => h5 ⟨c, rfl⟩
  have hlb : ∀ x, x ∈ (C.lev.Lb : Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)) ↔ x ∈ baseL B (B.R.N B.R.m) (X.piT u) := fun x => by
    have := hk.lb () x
    rw [← h1] at this
    exact this
  have hoff' : ∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (k () * t) = 1 := fun v hT hnQ => by
    rw [map_mul, hoff v hT, one_mul]
    refine bc_prV_eq_one fun w hw i j => htw w (fun hwQ => hnQ ⟨w, hwQ, hw⟩) (fun hwQ => hnQ ⟨conjPrime₂ w, hwQ, ?_⟩) i j
    rw [← hw]
    exact hunder w
  have hT' : ∀ (P : (B.primes X).vT u) (r j : Fin (B.R.N B.R.m)), r.1 + 1 = B.R.N B.R.m →
      HasRes P.1 (adAt B.host.F P.1 (((k () * t)⁻¹ : GA B (B.R.N B.R.m)).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := fun P r j hr => by
    have hP1 : P.1 ∉ I.Q a := fun h => (hf _ h).1.1 P.2
    have hP2 : conjPrime₂ P.1 ∉ I.Q a := fun h => (hf _ h).1.2.2.1 (by rw [CharValCompare.conjP_conjP]; exact P.2)
    rw [localComponent_mul_inv_entry _ _ _ (localComponent_eq_one _ _ (htw _ hP1 hP2))]
    exact hkT P r j hr
  refine ⟨fun _ => ⟨C.lev, C.y, C.y_bij, C.y_lat, C.stabI, C.stabI_inj, C.stabI_range⟩, ⟨fun _ => k () * t, ?_, fun _ d g₁ g₂ hd he => GlobalTheory.T.pointOverX_has_adelicPoint_blockExtend_mul I hOk hPins l Z u a (k ()) t hkstd hoff hkT ht htP d g₁ g₂ hd he⟩, ?_, fun v hv => h3 v hv, ?_, ?_⟩
  · exact reads_top I u a N hdN hΘ K.lev.U K.lev.chi (k ()) t hkU hkQ ht hU hχ C.lev.Lb C.lev.U C.lev.chi (fun c => (C.y ⟨c, rfl⟩).1)
      (fun c s => (C.stabI ⟨c, rfl⟩ s).1) hlb (GlobalTheory.T.exists_ptOf_mul_K1_standard _ _ _ (k ()) t ht hkstd) hoff' hT' (fun c => by rw [hy5, hy]; exact hg c) (fun c => by rw [hy5]; exact hpt c)
      h2 h4 (fun c s => h6 ⟨c, rfl⟩ s)
  · intro c d g₁ g₂ hrep hd he
    have hp := GlobalTheory.T.pointOverX_has_adelicPoint_blockExtend_mul I hOk hPins l Z u a (k ()) t hkstd hoff hkT ht htP d g₁ g₂ hd he
    have hp2 : PtOf (y c * (k () * t)) (tilF I.sel (I.tup a) u d) := hrep ▸ hpt c
    have := top_base I u a N hdN hΘ K.lev.U (k ()) t hkU hkQ ht hU _ (y c) g₂ hp hp2
    show g₂⁻¹ * (C.y ⟨c, rfl⟩).1 ∈ C.lev.U
    rw [h2, hy5]
    exact this
  · exact root_top I u a N hdN hΘ K.lev.U K.lev.chi (k ()) t hU hχ hUle C.lev.U C.lev.chi h2 h4
  · intro κ κ' e hv
    have hx : κ.1 ∈ topU (K.lev.U : Subgroup (GA B (B.R.N B.R.m))) t ((I.Tp a).levQ B.R.m) (I.dTop a) := h2 ▸ κ.2
    have e4 := h4 κ κ' ⟨κ.1, hx⟩ e rfl
    have e5 := (hchiQ).2 ⟨κ.1, hx⟩ (fun P => by
      have := TwTop.localComponent_congr (F := B.host.F) P.1 (v := P.1.under (𝓞 B.host.F)) rfl (x := κ.1) (x' := 1)
        ((hv _ ((hQ _).2 ⟨P.1, P.2, rfl⟩)).trans (map_one _).symm)
      exact this.trans (map_one _))
    exact e4.trans ((congrArg (fun w => K.lev.chi κ' * w) e5).trans (mul_one _))

end GlobalTheory.Mem.Col2.TC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartLastStepTwistBasePointStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_lastStep_twistBasePoint : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClsTied (D := (I.rec7 l Z)) u B.R.m le_rfl), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∃ k, I.Reads u I.mu0 B.R.m (fun _ => ()) (fun _ => K.lev.Lb) (fun _ => K.lev.U) (fun _ => K.lev.chi) (fun c => (K.y c).1) (fun c s => (K.stabI c s).1) k) → ∃ (K1 : ∀ β : Unit, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) B.R.m le_rfl (fun c : {c // (fun _ : (I.stp u a B.R.m).Cl => ()) c = β} => (I.chain l u a).stab B.R.m c.1) (fun c => latCrd (I.rec7 l Z) B.R.m le_rfl (I.latAt u a B.R.m c.1))), (∃ k, I.Reads u a B.R.m (fun _ => ()) (fun β => (K1 β).lev.Lb) (fun β => (K1 β).lev.U) (fun β => (K1 β).lev.chi) (fun c => ((K1 ()).y ⟨c, rfl⟩).1) (fun c s => ((K1 ()).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d → IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 → PtOf (g * k β) (tilF I.sel (I.tup a) u d)) ∧ I.TopBase l Z u a (K1 ()).lev.U (fun c => ((K1 ()).y ⟨c, rfl⟩).1) ∧ (∀ v, v ∉ Q → (K1 ()).lev.Uloc v = K.lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K1 ()).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K1 ()).lev.U) (κ' : K.lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K1 ()).lev.chi κ = K.lev.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.chart_twm | exact GlobalTheory.Mem.Col2.TC.chart_twm | (intros; apply GlobalTheory.Mem.Col2.TC.chart_twm <;> assumption)
end
