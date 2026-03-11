DIR_OF_TPTP=$1
CVC5_PATH=$2
for f in `find $DIR_OF_TPTP -name "*.p"`
do
  echo $f
  ./$CVC5_PATH -o raw-benchmark --parse-only --output-lang=smt2 $f > $f.smt2
done
