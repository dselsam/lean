# on branch clsgrph from https://github.com/Kha/lean

cd build/release \
   && make clean \
   && make clean-olean \
   && echo "Building lean3..." \
   && make -j8 bin_lean \
   && cd ../../../mathlib \
   && bash purge_olean.sh \
   && git pull origin master \
   && cd src \
   && rm -f out err \
   && echo "Building mathlib..." \
   && LEAN_PATH=.:../../lean3/library ../../lean3/bin/lean --recursive > out 2> err \
   && cd ../../lean3 \
   && echo "Creating json..." \
   && cat ../mathlib/src/err | perl -p0e 's/,\s*([]}])/\1/g' > mathlib.json \
   && echo "Processing mathlib.json..." \
   && ./process.py mathlib.json \
   && echo "Running  mathlib.json..." \
   && cat mathlib.json | jq '.items | unique | sort_by(.steps) | .[-50:] | map({kind: .kind, type: .type, max_depth: .max_depth, steps: .steps})'
