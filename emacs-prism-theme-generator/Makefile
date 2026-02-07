.PHONY: package clean test

VERSION := $(shell grep 'Version:' prism-theme-generator.el | cut -d' ' -f3)

package:
	@echo "Packaging Emacs package..."
	@tar -czf prism-theme-generator-emacs-$(VERSION).tar.gz \
		prism-theme-generator.el README.md LICENSE \
		--exclude="*.git*" --exclude="*.DS_Store" --exclude="*.swp" --exclude="*.swo"

clean:
	@rm -f *.tar.gz *.zip

test:
	@emacs --batch --eval "(add-to-list 'load-path \".\")" \
	       --eval "(require 'prism-theme-generator)" \
	       --eval "(prism-theme-generator-mode)" \
	       --eval "(message \"Plugin loaded successfully\")"
