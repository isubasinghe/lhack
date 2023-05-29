import Lake
open Lake DSL

package lhack {
  -- add package configuration options here
}

lean_lib Lhack {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe lhack {
  root := `Main
}
