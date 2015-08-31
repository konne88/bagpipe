There are a bunch of BGP simulators: C-BGP, Zebra, Quagga, XORP, and OpenBGPd. It is also possible to use network emulation environments such as IMUNES to run multiple instances of BGP daemons on a single workstation. 

Many BGP simulators simulate actual router operating system and networks with TCP/IP. C-BGP is at the right abstraction level for Bagpipe, it just simulates BGP. 

C-BGP is quite old, but stuff runs fine. There is [tutorial][T] that's pretty good, and a paper [Modeling the routing of an Autonomous System with C-BGP][M] (that I didn't read).

In BGP, policies are implemented via [rules][R]. 

Run C-BGP with:

    docker-machine create -d virtualbox --virtualbox-memory 2048 dev
    eval "$(docker-machine env dev)"
    docker build -t cbgp .; docker run -ti cbgp cbgp -c test.conf
    
[T]: http://c-bgp.sourceforge.net/tutorial.php
[R]: http://c-bgp.sourceforge.net/doc/html/nodes/bgp_router_peer_filter_add-rule.html
[M]: http://dl.acm.org/citation.cfm?id=2329745

