{ mkCoqDerivation, coq, mathcomp-ssreflect, mathcomp-algebra, stdlib,
  version ? null,
}:

mkCoqDerivation {
  pname = "zify";
  defaultVersion = "null";
  inherit version;
  propagatedBuildInputs = [ mathcomp-ssreflect mathcomp-algebra stdlib ];
}
