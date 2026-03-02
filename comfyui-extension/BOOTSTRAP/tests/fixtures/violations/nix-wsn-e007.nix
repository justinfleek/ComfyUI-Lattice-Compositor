# Violation: WSN-E007 - if/then/else in module config
{ config, lib, ... }:
{
  config = if config.enable then { } else { };
}
