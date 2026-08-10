TIMEOUT ?= 120

.PHONY: clean test

clean:
	find . \( -name "*.aux" -o -name "*.glob" -o -name "*.vo" -o -name "*.vok" -o -name "*.vos" \) -delete

test:
	bash regress/calltests.sh $(TIMEOUT)
