module Test where

import Compass.Core

main :: forall a. IO Unit
main = do
  let user : Compass.Core.User := { id := "test", org_id := "test-org", name := "Test", email := "test@test.com", role := .ADMIN, mfa_enabled := true, daily_budget := 10.0, monthly_budget := 100.0, is_active := true, created_at := "2026-01-01", updated_at := "2026-01-01" }
  IO.println "PureScript import test: SUCCESS"
