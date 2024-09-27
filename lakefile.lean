import Lake
open Lake DSL

package "WhitneyGraustein" where
  -- add package configuration options here

require SphereEversion from git "https://github.com/leanprover-community/sphere-eversion"@"master"

lean_lib «WhitneyGraustein» where
  -- add library configuration options here

@[default_target]
lean_exe "whitneygraustein" where
  root := `Main
