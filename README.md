VeriDrone
==========

This contains the verification work discussed in our EMSOFT 15 submission. See below for information on installing dependencies and the layout of the directories.

Dependencies
------------

You will need csdp:
```
apt-get install coinor-csdp
```

And you will need Z3, which you can get here:

[[http://z3.codeplex.com/releases]]

Coq Dependencies
----------------

ExtLib

Charge (revision a21ed562baf247c8bc5677fc55a594325799e193)
You can get this by running ```./get-charge.sh``

Directory Structure
-------------------
This project contains three directories:

1. tla - our embedding of TLA (rTLA), proof rules, automation, and some arithmetic facts
2. tlaexamples - our Sys abstraction and proof rules for our Sys (System.v) as well as various systems specified and verified using Sys that are discussed in our submission.
3. Z3-plugin - a plugin for running Z3 on real arithmetic goals from Coq.
