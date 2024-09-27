import Lake
open Lake DSL

package "WhitneyGraustein" where
  -- add package configuration options here

lean_lib «WhitneyGraustein» where
  -- add library configuration options here

@[default_target]
lean_exe "whitneygraustein" where
  root := `Main
