-- |
-- Module      : prism-theme-generator
-- Description : Neovim plugin for generating base16 color themes
-- 
-- Generates themes using Lean4-proven color mathematics
-- via Haskell FFI bridge
--

local M = {}

local config = {
  python_bridge_path = os.getenv('PRISM_PYTHON_BRIDGE') or 'python',
  haskell_lib_path = os.getenv('PRISM_FFI_LIB') or 'libprism-ffi.so',
  default_monitor_type = 'OLED',
  default_mode = 'dark',
  auto_apply = false,
}

-- ============================================================================
-- FFI BRIDGE
-- ============================================================================

local function generate_theme_variants(config_json)
  -- Get absolute path to FFI script
  -- Try multiple methods to find the script path
  local script_path = config.haskell_lib_path
  if script_path == "libprism-ffi.so" then
    -- Default: try to find relative to workspace root
    -- This assumes plugin is installed in a standard location
    local workspace_root = vim.fn.getcwd()
    script_path = workspace_root .. "/src/lattice/FFI/theme_generator_ffi.py"
    
    -- Alternative: use environment variable
    local env_path = os.getenv("PRISM_FFI_SCRIPT")
    if env_path and vim.fn.filereadable(env_path) == 1 then
      script_path = env_path
    end
  end
  
  local cmd = string.format(
    'echo %s | %s "%s"',
    vim.fn.shellescape(config_json),
    config.python_bridge_path,
    script_path
  )
  
  local handle = io.popen(cmd)
  if not handle then
    return nil, "Failed to execute Python bridge"
  end
  
  local result = handle:read("*a")
  handle:close()
  
  if not result or result == "" then
    return nil, "No result from Python bridge"
  end
  
  local ok, parsed = pcall(vim.fn.json_decode, result)
  if not ok then
    return nil, "Failed to parse JSON: " .. tostring(parsed)
  end
  
  if parsed.error then
    return nil, parsed.error
  end
  
  return parsed, nil
end

-- ============================================================================
-- UI COMPONENTS
-- ============================================================================

local function create_color_picker(title, callback)
  -- Simple color picker using Neovim's built-in color picker or external tool
  -- For now, use a simple input method
  vim.ui.input({
    prompt = title .. " (hex, e.g., #54aeff): ",
  }, function(input)
    if input and input ~= "" then
      callback(input)
    end
  end)
end

local function create_theme_generator_ui()
  local buf = vim.api.nvim_create_buf(false, true)
  local win = vim.api.nvim_open_win(buf, true, {
    relative = 'editor',
    width = 80,
    height = 30,
    col = 10,
    row = 5,
    style = 'minimal',
    border = 'rounded',
  })
  
  vim.api.nvim_buf_set_name(buf, 'Prism Theme Generator')
  
  local lines = {
    '╔══════════════════════════════════════════════════════════════════════════════╗',
    '║                    Prism Theme Generator                                     ║',
    '╠══════════════════════════════════════════════════════════════════════════════╣',
    '║                                                                              ║',
    '║  Base Color: [Select]                                                        ║',
    '║  Hero Color: [Select]                                                        ║',
    '║                                                                              ║',
    '║  Monitor Type: [OLED] [LCD]                                                 ║',
    '║  Black Balance: [=====●====] 11%                                            ║',
    '║                                                                              ║',
    '║  Theme Mode: [Dark] [Light]                                                 ║',
    '║                                                                              ║',
    '║  [Generate Themes]                                                           ║',
    '║                                                                              ║',
    '╚══════════════════════════════════════════════════════════════════════════════╝',
  }
  
  vim.api.nvim_buf_set_lines(buf, 0, -1, false, lines)
  vim.api.nvim_buf_set_option(buf, 'modifiable', false)
  
  -- TODO: Add interactive keybindings and UI logic
end

-- ============================================================================
-- COMMANDS
-- ============================================================================

function M.generate_theme()
  create_theme_generator_ui()
end

function M.preview_theme()
  vim.notify("Theme preview not yet implemented", vim.log.levels.INFO)
end

function M.export_theme()
  vim.notify("Theme export not yet implemented", vim.log.levels.INFO)
end

-- ============================================================================
-- SETUP
-- ============================================================================

function M.setup(opts)
  config = vim.tbl_deep_extend('force', config, opts or {})
  
  -- Register commands
  vim.api.nvim_create_user_command('PrismThemeGenerate', M.generate_theme, {
    desc = 'Generate base16 color themes',
  })
  
  vim.api.nvim_create_user_command('PrismThemePreview', M.preview_theme, {
    desc = 'Preview generated theme',
  })
  
  vim.api.nvim_create_user_command('PrismThemeExport', M.export_theme, {
    desc = 'Export theme to file',
  })
end

return M
