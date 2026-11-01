module

public import ThreeColour.PhysicalChecks.Source0
public import ThreeColour.PhysicalChecks.Source1
public import ThreeColour.PhysicalChecks.Source2
public import ThreeColour.PhysicalChecks.Source3
public import ThreeColour.PhysicalChecks.Source4
public import ThreeColour.PhysicalChecks.Source5
public import ThreeColour.PhysicalChecks.Source6
public import ThreeColour.PhysicalChecks.Source7
public import ThreeColour.PhysicalChecks.Source8
public import ThreeColour.PhysicalChecks.Source9
public import ThreeColour.PhysicalChecks.Source10
public import ThreeColour.PhysicalChecks.Source11
public import ThreeColour.PhysicalChecks.Source12
public import ThreeColour.PhysicalChecks.Source13
public import ThreeColour.PhysicalChecks.Source14
public import ThreeColour.PhysicalChecks.Source15
public import ThreeColour.PhysicalChecks.Source16
public import ThreeColour.PhysicalChecks.Source17
public import ThreeColour.PhysicalChecks.Source18
public import ThreeColour.PhysicalChecks.Source19
public import ThreeColour.PhysicalChecks.Source20
public import ThreeColour.PhysicalChecks.Source21
public import ThreeColour.PhysicalChecks.Source22
public import ThreeColour.PhysicalChecks.Source23
public import ThreeColour.PhysicalChecks.Source24
public import ThreeColour.PhysicalChecks.Source25
public import ThreeColour.PhysicalChecks.Source26
public import ThreeColour.PhysicalChecks.Source27
public import ThreeColour.PhysicalChecks.Source28
public import ThreeColour.PhysicalChecks.Source29
public import ThreeColour.PhysicalChecks.Source30
public import ThreeColour.PhysicalChecks.Source31
public import ThreeColour.PhysicalChecks.Source32
public import ThreeColour.PhysicalChecks.Source33
public import ThreeColour.PhysicalChecks.Source34
public import ThreeColour.PhysicalChecks.Source35
public import ThreeColour.PhysicalChecks.Source36
public import ThreeColour.PhysicalChecks.Source37
public import ThreeColour.PhysicalChecks.Source38
public import ThreeColour.PhysicalChecks.Source39
public import ThreeColour.PhysicalChecks.Source40
public import ThreeColour.PhysicalChecks.Source41
public import ThreeColour.PhysicalChecks.Source42
public import ThreeColour.PhysicalChecks.Source43
public import ThreeColour.PhysicalChecks.Source44
public import ThreeColour.PhysicalChecks.Source45
public import ThreeColour.PhysicalChecks.Source46
public import ThreeColour.PhysicalChecks.Source47
public import ThreeColour.PhysicalChecks.Source48
public import ThreeColour.PhysicalChecks.Source49
public import ThreeColour.PhysicalChecks.Source50
public import ThreeColour.PhysicalChecks.Source51
public import ThreeColour.PhysicalChecks.Source52
public import ThreeColour.PhysicalChecks.Source53
public import ThreeColour.PhysicalChecks.Source54
public import ThreeColour.PhysicalChecks.Source55
public import ThreeColour.PhysicalChecks.Source56
public import ThreeColour.PhysicalChecks.Source57
public import ThreeColour.PhysicalChecks.Source58
public import ThreeColour.PhysicalChecks.Source59
public import ThreeColour.PhysicalChecks.Source60
public import ThreeColour.PhysicalChecks.Source61
public import ThreeColour.PhysicalChecks.Source62
public import ThreeColour.PhysicalChecks.Source63
public import ThreeColour.PhysicalChecks.Source64
public import ThreeColour.PhysicalChecks.Source65
public import ThreeColour.PhysicalChecks.Source66
public import ThreeColour.PhysicalChecks.Source67

@[expose] public section

namespace ThreeColour
theorem fits_physical (t : Target) (k : Slot) (i : Source) :
    fits t k i = true ↔ ∃ r : Fin 24, FaceFits t i k r := by
  fin_cases i
  · exact fits_physical_0 t k
  · exact fits_physical_1 t k
  · exact fits_physical_2 t k
  · exact fits_physical_3 t k
  · exact fits_physical_4 t k
  · exact fits_physical_5 t k
  · exact fits_physical_6 t k
  · exact fits_physical_7 t k
  · exact fits_physical_8 t k
  · exact fits_physical_9 t k
  · exact fits_physical_10 t k
  · exact fits_physical_11 t k
  · exact fits_physical_12 t k
  · exact fits_physical_13 t k
  · exact fits_physical_14 t k
  · exact fits_physical_15 t k
  · exact fits_physical_16 t k
  · exact fits_physical_17 t k
  · exact fits_physical_18 t k
  · exact fits_physical_19 t k
  · exact fits_physical_20 t k
  · exact fits_physical_21 t k
  · exact fits_physical_22 t k
  · exact fits_physical_23 t k
  · exact fits_physical_24 t k
  · exact fits_physical_25 t k
  · exact fits_physical_26 t k
  · exact fits_physical_27 t k
  · exact fits_physical_28 t k
  · exact fits_physical_29 t k
  · exact fits_physical_30 t k
  · exact fits_physical_31 t k
  · exact fits_physical_32 t k
  · exact fits_physical_33 t k
  · exact fits_physical_34 t k
  · exact fits_physical_35 t k
  · exact fits_physical_36 t k
  · exact fits_physical_37 t k
  · exact fits_physical_38 t k
  · exact fits_physical_39 t k
  · exact fits_physical_40 t k
  · exact fits_physical_41 t k
  · exact fits_physical_42 t k
  · exact fits_physical_43 t k
  · exact fits_physical_44 t k
  · exact fits_physical_45 t k
  · exact fits_physical_46 t k
  · exact fits_physical_47 t k
  · exact fits_physical_48 t k
  · exact fits_physical_49 t k
  · exact fits_physical_50 t k
  · exact fits_physical_51 t k
  · exact fits_physical_52 t k
  · exact fits_physical_53 t k
  · exact fits_physical_54 t k
  · exact fits_physical_55 t k
  · exact fits_physical_56 t k
  · exact fits_physical_57 t k
  · exact fits_physical_58 t k
  · exact fits_physical_59 t k
  · exact fits_physical_60 t k
  · exact fits_physical_61 t k
  · exact fits_physical_62 t k
  · exact fits_physical_63 t k
  · exact fits_physical_64 t k
  · exact fits_physical_65 t k
  · exact fits_physical_66 t k
  · exact fits_physical_67 t k
theorem solvable_iff_physical (x : Inventory) : Solvable x ↔ PhysicalSolvable x := by
  constructor
  · rintro ⟨t,f,hf⟩
    exact ⟨t,f,fun k => (fits_physical t k (f k).1).mp (hf k)⟩
  · rintro ⟨t,f,hf⟩
    exact ⟨t,f,fun k => (fits_physical t k (f k).1).mpr (hf k)⟩
end ThreeColour
