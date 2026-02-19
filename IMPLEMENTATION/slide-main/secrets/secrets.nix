# Secrets configuration for agenix
#
# To add a new secret:
#   1. Add entry to this file
#   2. Run: cd secrets && agenix -e <secret-name>.age
#   3. The secret will be encrypted with the keys listed below
#
# To re-key all secrets (after adding new keys):
#   cd secrets && agenix -r
#
let
  # Developer SSH public keys
  b7r6 = "ssh-ed25519 AAAAC3NzaC1lZDI1NTE5AAAAINbn+XF6n9v9VKLFGLBVz+G1LyL6GlcgZbIwhP89PPsp";

  # All developers who can decrypt secrets
  users = [ b7r6 ];
in
{
  "openrouter-api-key.age".publicKeys = users;
}
