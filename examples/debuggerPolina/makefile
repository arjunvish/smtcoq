debug: parse
	python3 debugger.py $(ARGS)
parse: gen
	python3 parse_driver.py $(ARGS)
gen: 
	python3 file_generate.py $(ARGS)
clean:
	rm $(ARGS)/$(ARGS)run.*
	rm $(ARGS)/$(ARGS).txt
