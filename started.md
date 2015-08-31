---
content_type: md
permalink: /started.html
layout: main
header_style: height:60px;
click: download('/bagpipe/');
title: "Getting Started with Bagpipe"
topnav:
- text: Run
  url: javascript:scrollToHeading('run-bagpipe')
- text: Understand
  url: javascript:scrollToHeading('understand-policies')
- text: Love
  url: javascript:scrollToHeading('know-the-benefits')
---

Getting Started With Bagpipe
----------------------------

Bagpipe enables Autonomous System (AS) administrators to verify policies for their BGP router configurations. This post shows how to run Bagpipe, explains  how to write policies, and lists the benefits of using Bagpipe.

<!--more-->

### Run Bagpipe

This section shows how to run Bagpipe to verify that the [Internet2 AS][I2] never uses "martian" routing information --- routing information for invalid prefixes such as localhost. To verify that the "no martian" policy holds for Internet2, first download the file [example.tar][EX] that contains the policy and Internet2's configurations, and and then pass that file to Bagpipe:

    cat example.tar | docker run -i konne/bagpipe verify atla

The above command assumes an installation of docker. Docker installation instructions are provided [here][DOCKER]. I promise installing and understanding docker doesn't take long, and it will be beneficial even if you won't end up using Bagpipe.

Bagpipe first downloads some resources (this takes a while for the first time you start Bagpipe), and then verifies the "no martian" policy for the Atlanta `atla` router of Internet2 (replace `atla` with `all` to verify the policy for all routers of Internet2). The output of Bagpipe should contain:

    total number of checks 39
    check 0
    check 1
    check 2
    ...
    check 38
    holds

### Understand Policies

The "no martian" policy from above is defined as follows:

    (define (no-martian r p al)
      (if (and (martian? p) (available? al))
        false
        true))

A policy is a function that takes a portion of router state and returns `true` if the state is acceptable and `false` otherwise. The router state passed to the no `no-martian` policy is a router's local RIB, which assigns routing information to some prefixes. Concretely, the `no-martian` policy takes the potential routing information `al` assigned to prefix `p` in the local RIB of router `r`, and returns `false` if `p` is a martian `martian?` and the routing information for `p` is actually available `available?`.

We say that a policy _holds_ if it is `true` for every reachable router state. Bagpipe is an algorithm that efficiently checks whether a policy holds.

We have seen that the `no-martian` policy holds for Internet2. This is because the import rule for each of Internet2's neighbors applies the `SANITY-IN` rule, which discards routing information for "martian" prefixes. Let's see what happens if we remove these sanity checks from Internet2's router configurations, by running:

    cat example.tar | docker run -i konne/bagpipe verify atla-no-sanity

The output of Bagpipe should look like the following:

    total number of checks 39
    check 0
    check 1
    check 2
    ...
    check 38
                                   
    149.165.254.20                64.57.28.243
        ______                       ______
       |      |                     |      |
       | a0  -|---------------------|-> al |
       |______|                     |______|

    p  = 244.9.3.0/16
    a0 = {pref: 0, coms: [INTERNET2-INFINERA], path: []}
    al = {pref: 200, coms: [INTERNET2-INFINERA], path: []}

Bagpipe prints a counter example for which the policy does not hold (your counter example may be different). Remember that such a counter example is some reachable router state for which the `no-martian` policy returns `false`.

The counter example is the routing information `al` assigned to prefix `244.9.3.0/16` in the local RIB of router `64.57.28.243`. `al`'s LOCAL_PREF attribute is set to `0`, the COMMUNITIES attribute has the `INTERNET2-INFINERA` community set, and the AS_PATH is empty. For this to be a counter example, it must not be accepted by the `no-martian` policy, and it must be reachable.

- The counter example is indeed not accepted by the `no-martian` policy, because `p` is reserved as part of the Class E address space and thus "martian" (see [RFC 3330][RFC3330]). Therefore, `(no-martian (ip 64 57 28 243) (cidr (ip 244 9 3 0) 16) al)` evaluates to `false`.

- The counter example is also reachable, because Internet2's neighbor `149.165.254.20` can send an update message containing the routing information `a0` which is imported by `64.57.28.243` as `al`.

Bagpipe is configured with a _setup file_. In the example above, this was the [example.tar][EX] file. A setup file is a tar archive that contains a [Racket][RT] program called `setup.rkt`. Bagpipe runs two functions in `setup.rkt`:

- `policy` provides the policy to be verified
- `as` loads the AS's router configurations

In the examples above, these two functions are:

    (define (policy args)
      no-martian)

    (define (as args)
      (cond
        [(equal? (first args) "all") (load-all)]
        [(equal? (first args) "atla") (load-atla)]
        [(equal? (first args) "atla-no-sanity") (load-atla-no-sanity)]))

Bagpipe forwards its command-line arguments to both functions (in the examples above the command-line arguments are `atla` and `atla-no-sanity`). The `policy` function ignores the command-line arguments and returns the `no-martian` policy. The `as` function parses the command-line arguments and calls `load-as` on the appropriate router configurations.

### Know the Benefits

Running Bagpipe on your BGP router configurations has several benefits:

- Bagpipe's policies are _concise_ and _centralized_. For example, by using Bagpipe an Internet2 administrator only has to manually verify the `no-martian` policy instead of having to manually verify that every duplicate of the `SANITY-IN` rule in every router configuration is correct and actually used by every neighbor of every router.
- Bagpipe's policies are checked statically and can thus improve _performance_. For example, by using Bagpipe Internet2 can remove some unnecessary `SANITY-IN` checks for those neighbors that block "martian" prefixes with other rules.
- Bagpipe's policies _compose_ nicely. If you check your configuration for multiple policies you know that all of them hold, if you add multiple rules to a neighbor they interfere according to the order of execution. For example, a rule executed first might accept routing informations that would be discarded by a later rule.

This is post only covers simple policies for local RIBs. Bagpipe also supports more complex policies for adjacent RIBs in and out. By using these advanced features policies such as the Gao Rexford Model can be verified. If you want to learn more, run into any problems, or have feedback, please contact us!

[RT]: http://racket-lang.org/
[EX]: assets/example.tar
[DOCKER]: https://docs.docker.com/installation/
[I2]: http://www.internet2.edu/
[RFC3330]: https://tools.ietf.org/html/rfc3330
