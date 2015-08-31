Project only the BGP relevant parts of the Juniper configurations with:

    cabal run project internet2/*.conf

Infer the topology and plot it using dot with:

    cabal run infer topology internet2/*.conf > out.dot
    circo -Tpdf out.dot > out.pdf
    open out.pdf

Infer contracts with:

    cabal run infer contracts internet2/*.conf

Inject new commands into the existing configurations with:

    cabal run inject add internet2/seat.conf "protocols bgp neighbor a.b.c.d {}" "protocols bgp neighbor a.b.c.d local-preference 400 ;"

