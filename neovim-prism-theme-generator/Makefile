.PHONY: package clean test

package:
	@echo "Packaging Neovim plugin..."
	@zip -r prism-theme-generator-neovim-0.1.0.zip \
		lua/ plugin/ README.md LICENSE \
		-x "*.git*" "*.DS_Store" "*.swp" "*.swo"

clean:
	@rm -f *.zip

test:
	@nvim --headless --cmd "set rtp+=." --cmd "lua require('prism-theme-generator').setup()" -c "qa"
