with (import <nixpkgs> {}).lib;
{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "mathcomp-zify";

  ## The attribute for coq compat shim, default to attribute
  ## set this when you need both to differ
  ## (for instance "rocq-elpi" and "coq-elpi")
  # coq-attribute = "mathcomp-zify";

  ## Set this when the package has no rocqPackages version yet
  ## (either in nixpkgs or in .nix/rocq-overlays)
  # no-rocq-yet = true;

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/rocq-overlays` or `.nix/coq-overlays`
  ##     should be preferred then.
  # buildInputs = [ ];

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "9.0-2.5.0";

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles = let
    ## The combinations of MathComp and Rocq versions we test
    matrix = {
      "2.3.0" = ["8.18" "8.19" "8.20"];
      "2.4.0" = ["8.19" "8.20" "9.0" "9.1"];
      "2.5.0" = ["8.20" "9.0" "9.1"];
      "master" = ["9.0" "9.1" "master"];
    };
    ## The versions of packages we need for each version of Rocq
    rocq-bundles = {};
    ## The versions of packages we need for each version of MathComp
    mc-bundles = {}; in
    attrsets.concatMapAttrs (mc: lists.foldr (rocq: bs: bs // {
      ${rocq + "-" + mc}.coqPackages =
        { coq.override.version = rocq;
          mathcomp-ssreflect.override.version = mc; }
        // rocq-bundles.${rocq} or {} // mc-bundles.${mc} or {};
    }) {}) matrix;

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};
  
  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  # cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
  
  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"
  
  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
