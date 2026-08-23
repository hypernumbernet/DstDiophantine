/-
Copyright (c) 2026 DstDiophantine contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DstDiophantine contributors
-/
import DstDiophantine.Algebra.LorentzDim

/-!
# Massless string spectrum labels (ℕ counts only)

Textbook SO(8) little-group dimensions and heterotic gauge adjoint dimensions.
No worldsheet, no GSO derivation, no root-system construction.
-/

namespace DstDiophantine

namespace Logic

namespace StringSpectrum

/-- Vector representation of the massless NS sector. Literature: `8_v`. -/
def eightV : ℕ := 8

/-- Spinor representation of the massless R sector. Literature: `8_s`. -/
def eightS : ℕ := 8

/-- Conjugate spinor. Literature: `8_c`. -/
def eightC : ℕ := 8

/-- Closed-string massless bosonic dof (Type II). Literature value. -/
def masslessBosonDof : ℕ := 128

/-- Closed-string massless fermionic dof (Type II). Literature value. -/
def masslessFermionDof : ℕ := 128

/-- Adjoint dimension of `E₈`. Literature value; root system not formalised. -/
def e8Adj : ℕ := 248

/-- Adjoint dimension of `E₈ × E₈`. -/
def e8e8Adj : ℕ := 2 * e8Adj

/-- Adjoint dimension of `SO(32)`. -/
def so32Adj : ℕ := 496

/-- Superstring critical spacetime dimension (literature; not derived here). -/
def superstringCriticalDim : ℕ := 10

/-- Even part of 10D N=1 Super-Poincaré = `iso(9,1)`. -/
def superPoincareEvenDim : ℕ := LorentzDim.iso91Dim

/-- Odd part: one Majorana–Weyl supercharge (real 16). -/
def superPoincareOddDim : ℕ := 16

/-- Total N=1 Super-Poincaré generator count label. -/
def superPoincareN1Dim : ℕ := superPoincareEvenDim + superPoincareOddDim

theorem massless_bose_fermi_match : masslessBosonDof = masslessFermionDof := rfl

theorem e8e8Adj_eq : e8e8Adj = 496 := by decide

theorem e8e8_eq_so32 : e8e8Adj = so32Adj := by decide

theorem superPoincareN1Dim_eq : superPoincareN1Dim = 71 := by
  simp [superPoincareN1Dim, superPoincareEvenDim, superPoincareOddDim,
    LorentzDim.iso91Dim, LorentzDim.isoDim, LorentzDim.soDim]

theorem superPoincareN1_ne_pgaGenerators :
    superPoincareN1Dim ≠ LorentzDim.pgaGeneratorCount := by
  rw [superPoincareN1Dim_eq, LorentzDim.pgaGeneratorCount_eq]
  decide

/-- Light-cone `8_v + 8_s` versus DST torsion-parameter count `6`. -/
theorem lightCone_ne_dstGenerators : eightV + eightS ≠ 6 :=
  LorentzDim.lightCone_ne_torsionGenerators

end StringSpectrum

end Logic

end DstDiophantine
