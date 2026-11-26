module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Assembly

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.TensTorsion
noncomputable section

open CategoryTheory NumberField
open scoped TensorProduct

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V.KH

def FgShift : Prop :=
  ∀ (G : Type) [Group G] (A s m : ℕ) (X : ℕ → Type) [∀ p, MulAction G (X p)]
    (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
    1 ≤ s → Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
    (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
    (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
    Module.Finite ℤ (groupHomology M m)

def HglFG : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], IsTotallyComplex L → ∀ N m : ℕ, Module.Finite ℤ (UpperTheory.V.K.HGL L N m)

end UpperTheory.FiniteGenerationAndTorsion

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.HglFGOf
noncomputable section

open CategoryTheory NumberField

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V UpperTheory.V.KH

theorem hglFG_of (h : FgShift) : HglFG := by
  intro L _ _ hL N m
  have := hL
  let C := faceCx (KT.Gm L N) (KT.Sx L N) (KT.Sx.face L N) KT.Sx.face_smul
  have hx := KT.sx_exact L N m
  exact h (KT.Gm L N) (KT.orbBound L N m) (3 ^ (KT.dd L N * N)) m (KT.Sx L N)
    (fun p => Rep.ofHom ⟨C.d p, fun g => LinearMap.ext fun f => C.d_equiv p g f⟩)
    (Rep.trivial ℤ (KT.Gm L N) ℤ)
    (Rep.ofHom ⟨C.ε, fun g => LinearMap.ext fun f => C.ε_equiv g f⟩)
    (Nat.one_le_pow _ _ (by norm_num)) hx.1 hx.2.1 hx.2.2
    (fun p hp => ⟨(KT.orb L N p).1, (KT.orb L N p).2.trans (KT.orbBound_mono L N hp)⟩)
    (fun p _ => KT.stab L N p)

end UpperTheory.FiniteGenerationAndTorsion

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.FinitelyGeneratedTorsion.FgShift
noncomputable section

open CategoryTheory

namespace UpperTheory.FiniteGenerationAndTorsion

open UpperTheory.V.KH

private theorem fgOfFin (N : Type) [AddCommGroup N] [i : Module ℤ N] (h : Module.Finite ℤ N) :
    AddGroup.FG N := by
  obtain rfl : i = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  exact Module.Finite.iff_addGroup_fg.1 h

private theorem finOfFg (N : Type) [AddCommGroup N] [i : Module ℤ N] (h : AddGroup.FG N) :
    Module.Finite ℤ N := by
  obtain rfl : i = AddCommGroup.toIntModule N := Subsingleton.elim _ _
  exact Module.Finite.iff_addGroup_fg.2 h

private theorem fgStep {P N Q : Type} [AddCommGroup P] [AddCommGroup N] [AddCommGroup Q]
    (u : P →+ N) (v : N →+ Q) (h : Function.Exact u v) [Finite P] (hQ : AddGroup.FG Q) :
    AddGroup.FG N := by
  have : Module.Finite ℤ Q := Module.Finite.iff_addGroup_fg.2 hQ
  have : Module.Finite ℤ P := Module.Finite.of_finite
  have hr : LinearMap.range u.toIntLinearMap = LinearMap.ker v.toIntLinearMap := by
    ext x
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    exact (h x).symm
  have : IsNoetherian ℤ N := isNoetherian_of_range_eq_ker _ _ hr
  exact Module.Finite.iff_addGroup_fg.1 inferInstance

private theorem fgBase (G : Type) [Group G] (X Y : Type) [MulAction G X] (A : ℕ) (M : Rep ℤ G)
    (e : permRep G X ⟶ M) (D : (Y →₀ ℤ) →ₗ[ℤ] (X →₀ ℤ)) (he : Function.Surjective e.hom)
    (hex : Function.Exact D e.hom) (ho : OrbLe G X A) :
    AddGroup.FG (groupHomology M 0) := by
  have := ho.1
  obtain ⟨φ⟩ := hZero G X M e (LinearMap.range D : Set (X →₀ ℤ)) he (fun f => by
    rw [Submodule.span_eq, LinearMap.mem_range]
    exact hex f)
  have hf := fgOfFin _ (inferInstance : Module.Finite ℤ ((MulAction.orbitRel.Quotient G X →₀ ℤ) ⧸
    Submodule.span ℤ (Finsupp.mapDomain
      (Quotient.mk (MulAction.orbitRel G X) : X → MulAction.orbitRel.Quotient G X) ''
        (LinearMap.range D : Set (X →₀ ℤ)))))
  exact AddGroup.fg_of_surjective (f := φ.symm.toAddMonoidHom) φ.symm.surjective

private theorem fg_homology_of_permutation_resolution (G : Type) [Group G] (A s : ℕ) (hs : 1 ≤ s) (m : ℕ) :
    ∀ (X : ℕ → Type) [∀ p, MulAction G (X p)]
      (d : ∀ p, permRep G (X (p + 1)) ⟶ permRep G (X p)) (M : Rep ℤ G) (e : permRep G (X 0) ⟶ M),
      Function.Surjective e.hom → Function.Exact (d 0).hom e.hom →
      (∀ p, p < m → Function.Exact (d (p + 1)).hom (d p).hom) →
      (∀ p, p ≤ m → OrbLe G (X p) A) → (∀ p, p ≤ m → StabLe G (X p) s) →
      AddGroup.FG (groupHomology M m) := by
  induction m with
  | zero =>
    intro X _ d M e he h0 _ ho _
    exact fgBase G (X 0) (X 1) A M e (d 0).hom.toLinearMap he h0 (ho 0 le_rfl)
  | succ m ih =>
    intro X _ d M e he h0 hx ho hst
    obtain ⟨K, p, i, hp, hi, hpi, hie⟩ := imageRep G _ _ _ (d 0) e h0
    have h1 : Function.Exact (d 1).hom p.hom := by
      intro y
      rw [← hx 0 (Nat.succ_pos m) y, ← hpi y]
      constructor
      · intro h; rw [h, map_zero]
      · intro h; exact hi (by rw [h, map_zero])
    have hK := ih (fun q => X (q + 1)) (fun q => d (q + 1)) K p hp h1
      (fun q hq => hx (q + 1) (by omega)) (fun q hq => ho (q + 1) (by omega))
      (fun q hq => hst (q + 1) (by omega))
    have hC := (permCard G s m A (X 0) (ho 0 (by omega)) (hst 0 (by omega)) hs).1
    obtain ⟨u, v, huv⟩ := (les G _ _ _ i e hi hie he m).2
    exact fgStep u v huv hK

theorem fgShift : FgShift := by
  intro G _ A s m X _ d M e hs he h0 hx ho hst
  exact finOfFg _ (fg_homology_of_permutation_resolution G A s hs m X d M e he h0 hx ho hst)

end UpperTheory.FiniteGenerationAndTorsion

end
end

noncomputable section

open NumberField UpperTheory.V.KT UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

theorem sFin_of : SBridge → SFin := by
  intro h L _ _ hL N k
  classical
  obtain ⟨θ, hsurj, hker, -⟩ := h k
  haveI : Module.Finite ℤ (grpH (Gm L N) (k + 1)) :=
    UpperTheory.FiniteGenerationAndTorsion.hglFG_of UpperTheory.FiniteGenerationAndTorsion.fgShift L hL N (k + 1)
  obtain ⟨t, ht⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℝ (ℝ ⊗[ℤ] ↑(grpH (Gm L N) (k + 1)))).FG)
  choose pre hpre using hsurj (Gm L N)
  refine ⟨t.image (fun m => ((pre m : ↥(bd (Gm L N) k).ker) : Chn (Gm L N) (k + 1))), ?_, ?_⟩
  · intro z hz
    obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp hz
    exact LinearMap.mem_ker.mp (pre m).2
  · intro z hz
    have hz' : z ∈ LinearMap.ker (bd (Gm L N) k) := LinearMap.mem_ker.mpr hz
    have hw : θ (Gm L N) ⟨z, hz'⟩ ∈ Submodule.span ℝ (θ (Gm L N) '' (pre '' (t : Set _))) := by
      rw [Set.image_image]
      simp only [hpre, Set.image_id']
      rw [ht]
      trivial
    rw [← Submodule.map_span] at hw
    obtain ⟨u, hu, hθ⟩ := hw
    refine ⟨(u : Chn (Gm L N) (k + 1)), ?_, ?_⟩
    · have hmem : (u : Chn (Gm L N) (k + 1)) ∈
          Submodule.map (LinearMap.ker (bd (Gm L N) k)).subtype (Submodule.span ℝ (pre '' (t : Set _))) :=
        ⟨u, hu, rfl⟩
      rw [Submodule.map_span, Set.image_image] at hmem
      simpa [Finset.coe_image] using hmem
    · have h0 : θ (Gm L N) (⟨z, hz'⟩ - u) = 0 := by
        rw [map_sub, hθ, sub_self]
      exact (hker (Gm L N) _).mp h0

end PositivityTheory.KB

end
