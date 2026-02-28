#!/usr/bin/env bash
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#                                                    // straylight // convention
# ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
#
# Generate and validate straylight convention headers.
# All lines are exactly 80 characters. Titles are right-aligned to column 80.
#
# Usage:
#   ./convention.sh header heavy "// module // name"
#   ./convention.sh header double "// section // name"
#   ./convention.sh header light "// subsection"
#   ./convention.sh title "// any // title"
#   ./convention.sh line heavy
#   ./convention.sh line double
#   ./convention.sh line light
#   ./convention.sh validate <file>
#
# ──────────────────────────────────────────────────────────────────────────────

set -euo pipefail

# ══════════════════════════════════════════════════════════════════════════════
#                                                                   // constants
# ══════════════════════════════════════════════════════════════════════════════

LINE_WIDTH=80
COMMENT_PREFIX="-- "
COMMENT_PREFIX_LEN=3
TITLE_PREFIX="--"
TITLE_PREFIX_LEN=2
LINE_CHAR_COUNT=$((LINE_WIDTH - COMMENT_PREFIX_LEN)) # 77

HEAVY_CHAR="━"
DOUBLE_CHAR="═"
LIGHT_CHAR="─"

# ══════════════════════════════════════════════════════════════════════════════
#                                                                  // generation
# ══════════════════════════════════════════════════════════════════════════════

# Generate a line of the specified type
# Usage: gen_line heavy|double|light
gen_line() {
	local type="$1"
	local char

	case "$type" in
	heavy) char="$HEAVY_CHAR" ;;
	double) char="$DOUBLE_CHAR" ;;
	light) char="$LIGHT_CHAR" ;;
	*)
		echo "Unknown line type: $type" >&2
		exit 1
		;;
	esac

	echo -n "$COMMENT_PREFIX"
	for ((i = 0; i < LINE_CHAR_COUNT; i++)); do
		echo -n "$char"
	done
	echo ""
}

# Generate a title line, right-aligned to column 80
# Usage: gen_title "// title // text"
gen_title() {
	local title="$1"
	local title_len=${#title}
	local spaces_needed=$((LINE_WIDTH - TITLE_PREFIX_LEN - title_len))

	if ((spaces_needed < 0)); then
		echo "Title too long: '$title' ($title_len chars, max $((LINE_WIDTH - TITLE_PREFIX_LEN)))" >&2
		exit 1
	fi

	echo -n "$TITLE_PREFIX"
	for ((i = 0; i < spaces_needed; i++)); do
		echo -n " "
	done
	echo "$title"
}

# Generate a complete header block
# Usage: gen_header heavy|double|light "// title"
gen_header() {
	local type="$1"
	local title="$2"

	gen_line "$type"
	gen_title "$title"
	gen_line "$type"
}

# ══════════════════════════════════════════════════════════════════════════════
#                                                                  // validation
# ══════════════════════════════════════════════════════════════════════════════

# Validate a single line
# Returns 0 if valid, 1 if invalid
validate_line() {
	local line="$1"
	local line_num="${2:-}"
	local len=${#line}

	if ((len != LINE_WIDTH)); then
		if [[ -n "$line_num" ]]; then
			echo "Line $line_num: expected $LINE_WIDTH chars, got $len"
		else
			echo "Expected $LINE_WIDTH chars, got $len"
		fi
		return 1
	fi

	return 0
}

# Validate all header lines in a file
# Usage: validate_file <file>
validate_file() {
	local file="$1"
	local errors=0
	local line_num=0

	while IFS= read -r line || [[ -n "$line" ]]; do
		line_num=$((line_num + 1))

		# Check lines that look like headers (start with comment prefix + box char)
		if [[ "$line" =~ ^"-- "[━═─] ]] || [[ "$line" =~ ^"--"[[:space:]]+"//".* ]]; then
			if ! validate_line "$line" "$line_num"; then
				errors=$((errors + 1))
			fi
		fi
	done <"$file"

	if ((errors > 0)); then
		echo ""
		echo "Found $errors header line(s) with incorrect length in $file"
		return 1
	else
		echo "All header lines in $file are valid (80 characters)"
		return 0
	fi
}

# ══════════════════════════════════════════════════════════════════════════════
#                                                                        // main
# ══════════════════════════════════════════════════════════════════════════════

usage() {
	cat <<EOF
Usage: $0 <command> [args]

Commands:
  header <type> <title>   Generate a complete header block
                          type: heavy, double, light
                          title: e.g., "// module // name"

  title <text>            Generate a single title line

  line <type>             Generate a single line
                          type: heavy, double, light

  validate <file>         Validate all header lines in a file

Examples:
  $0 header heavy "// hydrogen // color"
  $0 title "// constants"
  $0 line double
  $0 validate src/Hydrogen/Style/Color.purs
EOF
}

main() {
	if (($# < 1)); then
		usage
		exit 1
	fi

	local cmd="$1"
	shift

	case "$cmd" in
	header)
		if (($# != 2)); then
			echo "Usage: $0 header <type> <title>" >&2
			exit 1
		fi
		gen_header "$1" "$2"
		;;

	title)
		if (($# != 1)); then
			echo "Usage: $0 title <text>" >&2
			exit 1
		fi
		gen_title "$1"
		;;

	line)
		if (($# != 1)); then
			echo "Usage: $0 line <type>" >&2
			exit 1
		fi
		gen_line "$1"
		;;

	validate)
		if (($# != 1)); then
			echo "Usage: $0 validate <file>" >&2
			exit 1
		fi
		validate_file "$1"
		;;

	*)
		echo "Unknown command: $cmd" >&2
		usage
		exit 1
		;;
	esac
}

main "$@"
