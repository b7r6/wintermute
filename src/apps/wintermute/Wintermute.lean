/-
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
                                                        // WINTERMUTE // UMBRELLA
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━

    The hot-reload theme reconciler. Pure core:

      Color       integer HSL→RGB, exact ono-sendai generator port
      Theme       the 4-vector (heroHue × axisHue × luminance × register),
                  palette tables, register tokens, the hue-lock theorems
      Reconcile   the reconciler as an AbstractMachine + its invariants
      State       the state-file codec — the control plane IS a text file

    IO shell:

      Shell       mtime watch loop, adapters, atomic persist
━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
-/

import Wintermute.Color
import Wintermute.Theme
import Wintermute.Reconcile
import Wintermute.State
import Wintermute.Vectors
import Wintermute.Shell
