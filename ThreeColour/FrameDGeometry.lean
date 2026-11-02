module
public import ThreeColour.FrameCertificates
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ThreeColour

def dEdgePool (d : Colour) (j : Fin 3) : SourceSet :=
  edgePool (oppositeTarget d) (dEdgeRepresentative d j)

def dFramePools (d : Colour) : Fin 5 → SourceSet :=
  ![ordinary 0 ∪ eligible d, ordinary 1 ∪ eligible d,
    dEdgePool d 0, dEdgePool d 1, dEdgePool d 2]

lemma d_frame_counts : ∀ d : Colour,
    tagCount (dCornerTag d) = ![4,4,0,0,0] ∧
    tagCount (dEdgeTag d) = ![0,0,4,4,4] := by decide +kernel

lemma d_frame_corners : ∀ d p i,
    i ∈ dFramePools d (dCornerTag d p) → fits (oppositeTarget d) p i = true := by
  decide +kernel

lemma d_frame_edges : ∀ d p i,
    i ∈ dFramePools d (dEdgeTag d p) →
      HasEdge (sourceFaces i) (targetFaces (oppositeTarget d) (edgeFaces p 0))
        (targetFaces (oppositeTarget d) (edgeFaces p 1)) := by decide +kernel

lemma d_edge_pairs_cover : ∀ d (j l : Fin 3), j ≠ l →
    dEdgePool d j ∪ dEdgePool d l = Finset.univ := by decide +kernel

/-- Only one reduced checkerboard pool can miss a specified bichromatic edge. -/
lemma d_edge_complement : ∀ d j, ∃ h : Fin 6,
    dEdgePool d j ∪ checker h = Finset.univ := by decide +kernel

lemma checker_frame_corners : ∀ j p i, i ∈ checker j →
    fits (oppositeTarget (checkerFrameOmitted j)) p i = true := by decide +kernel

lemma checker_frame_edges : ∀ j p i, i ∈ checker j →
    HasEdge (sourceFaces i)
      (targetFaces (oppositeTarget (checkerFrameOmitted j)) (edgeFaces p 0))
      (targetFaces (oppositeTarget (checkerFrameOmitted j)) (edgeFaces p 1)) := by decide +kernel

end ThreeColour
