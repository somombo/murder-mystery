import Lake
open Lake DSL

package «mystery-murder» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- @[default_target]
lean_lib «MysteryMurder» {
  -- add any library configuration options here
}

@[default_target]
lean_exe «mystery-murder» {
  root := `Main
}
