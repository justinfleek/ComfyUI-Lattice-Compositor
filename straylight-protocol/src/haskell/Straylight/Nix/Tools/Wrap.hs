{-# LANGUAGE OverloadedStrings #-}

{- | Typed wrapProgram actions for build phases.

Pure data structures describing wrapProgram invocations. No runtime dependencies.

@
import qualified Straylight.Nix.Tools.Wrap as Wrap

postFixup
    [ Wrap.wrap "bin/mytool"
        [ Wrap.prefix "PATH" "${pkgs.coreutils}/bin"
        , Wrap.set "SSL_CERT_FILE" "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
        , Wrap.addFlags "--verbose"
        ]
    ]
@

The wrapProgram tool is automatically available in Nix build environments.
-}
module Straylight.Nix.Tools.Wrap (
    -- * Build phase actions
    wrap,

    -- * Wrap actions
    prefix,
    suffix,
    set,
    setDefault,
    unset,
    addFlags,
) where

import Straylight.Nix.Derivation (Action (..), WrapAction (..))
import Data.Text (Text)
import qualified Data.Text as T

-- | Wrap a program with environment modifications.
--
-- Example:
--   wrap "bin/mytool"
--     [ prefix "PATH" "${pkgs.coreutils}/bin"
--     , set "SSL_CERT_FILE" "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
--     ]
wrap :: Text -> [WrapAction] -> Action
wrap program wrapActions = Wrap program wrapActions

-- | Add to PATH prefix: --prefix VAR : value
--
-- Example:
--   prefix "PATH" "${pkgs.coreutils}/bin"
prefix :: Text -> Text -> WrapAction
prefix var value = WrapPrefix var value

-- | Add to PATH suffix: --suffix VAR : value
--
-- Example:
--   suffix "LD_LIBRARY_PATH" "${pkgs.zlib}/lib"
suffix :: Text -> Text -> WrapAction
suffix var value = WrapSuffix var value

-- | Set environment variable: --set VAR value
--
-- Example:
--   set "SSL_CERT_FILE" "${pkgs.cacert}/etc/ssl/certs/ca-bundle.crt"
set :: Text -> Text -> WrapAction
set var value = WrapSet var value

-- | Set default value (only if unset): --set-default VAR value
--
-- Example:
--   setDefault "EDITOR" "vim"
setDefault :: Text -> Text -> WrapAction
setDefault var value = WrapSetDefault var value

-- | Unset environment variable: --unset VAR
--
-- Example:
--   unset "DISPLAY"
unset :: Text -> WrapAction
unset var = WrapUnset var

-- | Add command-line flags: --add-flags "flags"
--
-- Example:
--   addFlags "--verbose --debug"
addFlags :: Text -> WrapAction
addFlags flags = WrapAddFlags flags
