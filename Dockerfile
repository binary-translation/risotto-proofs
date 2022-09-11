# Build with:
# > docker build . --tag=risotto-proofs
# 
# Run with:
# > docker run -it --rm risotto-proofs agda src/Main.agda --safe
# 
# Generate HTML with:
# > docker run -it --rm -v "$PWD/html:/proofs/html" risotto-proofs agda --html --html-dir=html src/Main.agda
FROM sourcedennis/agda-mini:2.6.2.1-1.7.1

WORKDIR /proofs
COPY --chown=proof:proof . /proofs
