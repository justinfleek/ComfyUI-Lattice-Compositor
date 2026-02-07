# Test 15: Nix with lib; in comment (should be ignored)
# with lib;  <- This is a comment

{ pkgs, lib }:

pkgs.mkDerivation {
  name = "test";
  
  # But actual violation should be caught:
  # with lib;  <- Still a comment
  
  # Real violation:
  with lib;  # This should be caught by WSN-E001
}
