let pkgs = import <nixpkgs> {};
    agda = pkgs.agda.withPackages (ps: [ ps.standard-library ps.cubical ]);
in pkgs.mkShell { buildInputs = [ agda ]; }
