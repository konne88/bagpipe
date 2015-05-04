---
content_type: md
permalink: /
layout: main
header_style: height:60px;
click: scrollTo(0)
title: "Bagpipe: BGP Policy Verification"
---

<img src="/bagpipe/assets/logo-large.png" style="float:left; margin:20px">

Bagpipe: BGP Policy Verification
================================

Internet Service Providers (ISPs) rely on the Border Gateway Protocol (BGP) to exchange routing information, which is necessary to deliver traffic over the Internet. The BGP behavior of an ISP's routers is determined by their configurations. Router misconfigurations have caused major monetary loss, performance degradation, service outages, and security violations. Some of the effects of misconfiguration are highly visible, such as the worldwide extended downtime of [YouTube in 2009][BGP-YT] and route hijacks by [China Telecom in 2010][BGP-CT10] and [2014][BGP-CT14]. Less visible is the high cost of developing and maintaining correct configurations, which requires checking invariants across hundreds of thousands of lines of configuration for all of an ISP's routers. 

Bagpipe enables an ISP to express its BGP policy in a domain-specific specification language and verify that its router configurations implement this policy. We evaluated Bagpipe on [Internet2][I2] and [Selfnet][SN], two ISPs with a combined total of over [100,000 lines of router configuration][RC]. We identified and expressed policies for these ISPs, and found 19 inconsistencies between the policies and the router configurations without issuing any false positives.

### Source

Bagpipe will be made open-source upon acceptance of the paper.

### People

<a class="person" href="http://konne.me">
  <span class="name">Konstantin Weitz</span><br/>
  <img class="profile" src="http://www.konne.me/assets/profile.png"/>
</a>

<a class="person" href="http://www.dougwoos.com/">
  <span class="name">Doug Woos</span><br/>
  <img class="profile" src="http://www.dougwoos.com/assets/me.jpeg"/>
</a>

<a class="person" href="http://homes.cs.washington.edu/~emina/" style="clear: both">
  <span class="name">Emina Torlak</span><br/>
  <img class="profile" src="http://homes.cs.washington.edu/~emina/images/emina.jpg"/>
</a>

<a class="person" href="https://homes.cs.washington.edu/~mernst/">
  <span class="name">Michael D. Ernst</span><br/>
  <img class="profile" src="http://www.cs.washington.edu/sites/default/files/mernst.jpg"/>
</a>

<a class="person" href="http://www.cs.washington.edu/people/faculty/arvind">
  <span class="name">Arvind Krishnamurthy</span><br/>
  <img class="profile" src="/bagpipe/assets/arvind.jpg"/>
</a>

<a class="person" href="https://homes.cs.washington.edu/~ztatlock/">
  <span class="name">Zachary Tatlock</span><br/>
  <img class="profile" src="/bagpipe/assets/ztatlock.png"/>
</a>

[SN]: https://www.selfnet.de/en
[I2]: http://www.internet2.edu/
[RC]: http://vn.grnoc.iu.edu/Internet2/configs/configs.html
[BGP-YT]: http://research.dyn.com/2008/02/pakistan-hijacks-youtube-1/ 
[BGP-CT10]: http://research.dyn.com/2010/11/chinas-18-minute-mystery/
[BGP-CT14]: http://research.dyn.com/2014/11/chinese-routing-errors-redirect-russian-traffic/
