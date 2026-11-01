module

public import ThreeColour.LowerData
public import MacMahon.Rotations

@[expose] public section

namespace ThreeColour
def reflection : Source → Source := fun i => (#[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 14, 15, 10, 11, 12, 16, 18, 17, 19, 21, 20, 22, 25, 26, 23, 24, 27, 28, 30, 29, 31, 32, 33, 34, 35, 36, 39, 40, 37, 38, 41, 42, 43, 46, 47, 44, 45, 48, 49, 50, 52, 51, 53, 54, 55, 56, 57, 58, 62, 60, 63, 59, 61, 64, 65, 67, 66] : Array (Source))[i.val]!
def reflectionRotation : Source → Fin 24 := fun i => (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 12, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 4, 4, 4, 4, 4, 4, 4, 5, 4, 6, 4, 12, 4, 4, 4, 4, 4, 5, 5, 4, 4, 4, 4, 4, 4, 6, 4, 4, 4, 4, 12, 5, 4, 5, 6, 4, 4, 4, 4, 4, 4, 4, 4, 4] : Array (Fin 24))[i.val]!
def reflectFace (f : Fin 6) : Fin 6 := if f.val < 2 then MacMahon.opposite f else f
def reflectInventory (x : Inventory) : Inventory := fun i => x (reflection i)
end ThreeColour
