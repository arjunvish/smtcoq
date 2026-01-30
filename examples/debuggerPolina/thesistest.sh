for i in {1..7}
do
	fname="thesistest${i}"
	time make ARGS=$fname
done
