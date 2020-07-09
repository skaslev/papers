let
  # Pin all dependencies by pinning the repository with packages.
  # builtins.fetchGit returns a path.
  nixpkgs = builtins.fetchGit {
    url = "https://github.com/NixOS/nixpkgs";
    rev = "3e420135172d10ea880c7c571c257d57cb7f1de2";
  };
  # Import the path to get the function that returns the set of all packages.
  # Brackets are optional.
  pkgs = (import nixpkgs) { };

  # texlive.combine is a function that you can use to, well, combine sets of texlive packages.
  # I decided to go with scheme-basic plus three more packages that your tex files use.
  tex = pkgs.texlive.combine {
    inherit (pkgs.texlive)
      scheme-basic

      fancyvrb
      todonotes
      ucs
      ;
  };
in
{
  # If you `nix-build --attr papers`, it will:
  # - build all pdfs using the recipe below
  # - symlink the resulting package into current directory as `result`
  papers = pkgs.stdenvNoCC.mkDerivation {
    name = "papers";
    src = pkgs.lib.sourceFilesBySuffices ./. [ "tex" ];
    buildInputs = [ tex ];
    buildPhase = ''
      for f in *.tex; do
        pdflatex $f
        pdflatex $f # do it twice to get outlines right
      done
    '';
    installPhase = ''
      mkdir -p $out
      cp *.pdf $out
    '';
  };

  # If you `nix-shell`, it will drop you in a shell with lean and tex packages.
  shell = pkgs.mkShell {
    buildInputs = [
      pkgs.lean
      tex
    ];
  };
}
