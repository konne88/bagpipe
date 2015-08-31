---
content_type: md
permalink: /
layout: main
header_style: height:240px;
click: scrollTo(0)
topnav:
- text: Get Started
  url: started.html
- text: Motivation
  url: javascript:scrollToHeading('motivation')
- text: People
  url: javascript:scrollToHeading('people')
title: Bagpipe
info: <div id="description" class="description">
        Bagpipe enables Autonomous System (AS) administrators to verify policies for their BGP router configurations.
      </div>
      <div class="buttons">
        <button type="button" class="btn btn-default" onclick="download('started.html')">Get Started with Bagpipe</button>
      </div>
---

### Motivation

Internet Service Providers (ISPs) rely on the Border Gateway Protocol (BGP) to exchange routing information, which is necessary to deliver traffic over the Internet. The BGP behavior of an ISP's routers is determined by their configurations. Router misconfigurations have caused major monetary loss, performance degradation, service outages, and security violations. Some of the effects of misconfiguration are highly visible, such as the worldwide extended downtime of [YouTube in 2009][BGP-YT] and route hijacks by [China Telecom in 2010][BGP-CT10] and [2014][BGP-CT14]. Less visible is the high cost of developing and maintaining correct configurations, which requires checking invariants across hundreds of thousands of lines of configuration for all of an ISP's routers. 

Bagpipe enables ISP administrators to express BGP policies in a domain-specific specification language and verify that the ISP's router configurations implement these policies. 

We have evaluated Bagpipe on [Internet2][I2] and [Selfnet][SN], two ISPs with a combined total of over [100,000 lines of router configuration][RC]. We identified and expressed policies for these ISPs, and found 19 inconsistencies between the policies and the router configurations without issuing any false positives.

Bagpipe is open-source and hosted on [GitHub][GH].

### People

If you have any question, want to be kept up-to date, or just want to say hi, email us at weitzkon at cs dot uw dot edu.

<a class="person" href="http://konne.me">
  <span class="name">Konstantin Weitz</span><br/>
  <img class="profile" src="http://www.konne.me/assets/profile.png"/>
</a>

<a class="person" href="http://www.dougwoos.com/">
  <span class="name">Doug Woos</span><br/>
  <img class="profile" src="http://www.dougwoos.com/assets/me.jpeg"/>
</a>

<a class="person" href="http://homes.cs.washington.edu/~emina/">
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

[GH]: https://github.com/konne88/bagpipe
[SN]: https://www.selfnet.de/en
[I2]: http://www.internet2.edu/
[RC]: http://vn.grnoc.iu.edu/Internet2/configs/configs.html
[BGP-YT]: http://research.dyn.com/2008/02/pakistan-hijacks-youtube-1/ 
[BGP-CT10]: http://research.dyn.com/2010/11/chinas-18-minute-mystery/
[BGP-CT14]: http://research.dyn.com/2014/11/chinese-routing-errors-redirect-russian-traffic/
