---
content_type: md
permalink: /bagpipe
layout: main
header_style: height:260px;
click: scrollTo(0)
title: Bagpipe: BGP Policy Verification
info: <div id="description" class="description">
        Bagpipe verifies BGP policies. 
      </div>
---

The CSS layout is weird.

Internet Service Providers (ISPs) rely on the Border Gateway Protocol (BGP) to exchange routing information, which is necessary to deliver traffic over the Internet. The BGP behavior of an ISP's routers is determined by their configurations. Router misconfigurations have caused major monetary loss, performance degradation, service outages, and security violations. Some of the effects of misconfiguration are highly visible, such as the worldwide extended downtime of [YouTube in 2009][BGP-YT] and route hijacks by [China Telecom in 2010][BGP-CT10] and [2014][BGP-CT14]. Less visible is the high cost of developing and maintaining correct configurations, which requires checking invariants across hundreds of thousands of lines of configuration for all of an ISP's routers. 

Bagpipe is a tool which enables an ISP to express its BGP policy in a domain-specific specification language and verify that its router configurations implement this policy. We evaluated Bagpipe on Internet2 and Selfnet, two ISPs with a combined total of over 100,000 lines of router configuration. We identified and expressed policies for these ISPs, and found 19 inconsistencies between the policies and the router configurations without issuing any false positives.

[BGP-YT]: http://research.dyn.com/2008/02/pakistan-hijacks-youtube-1/ 
[BGP-CT10]: http://research.dyn.com/2010/11/chinas-18-minute-mystery/
[BGP-CT14]: http://research.dyn.com/2014/11/chinese-routing-errors-redirect-russian-traffic/
