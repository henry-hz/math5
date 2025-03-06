




clean:
	lake exe cache clean
	lake clean
	rm -rf .lake

deps:
	lake exe cache get



