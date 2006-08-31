//Heuristic Search Data mining application in kdb+
//Example of a multi-1 opt. using generic GA framework

//system inputs
gen:5; //number of generations
complx:(floor (.5*count il)); //maximum complexity allowed for a random choice, e.g. 1/2 the number of variables
recssize:rndsize:10*mutesize:shftsize:elitesize:5*crossover:joinsize:5000; //set's sizes for components
sft:{1}; //how much should a point move on shift? e.g. if 2 the can be 0 1 2
bckts: 5; //number of buckets to  to place variables in

//utils
getfit:{(+/)db[`FIT]@x}; //get fitness for a given set
comb:{m:x:key x;do[y-1;x:{raze{y,/:(1+max y)_x}[y]each x}[x;m]];x}; //permutations
gettop25:{keepNdis[2;sm@distinct raze{where 3=x}each 4 xrank'sm (`FIT`cntbi)]}; //top quartile for each component of fitness 
gettop50:{keepNdis[2;sm@distinct raze{where 1<x}each 4 xrank'sm (`FIT`cntbi)]}; //top 2 quartiles for each component of fitness 
getbot50:{keepNdis[2;sm@distinct raze{where 1>x}each 4 xrank'sm (`FIT`cntbi)]}; //bottom 2 quartiles for each component of fitness 
keepNdis:{[n;t](+)(cols t)!flip where n&count each group flip value flip t}; //keep n distinct record from t
memclr:{![`.;();0b;enlist x]}; //clear memory used 
indx2eng:{{pairs[x@0]x@1}@/:x}; //lookup the english version of a solution using index

//GA core functions: there are more efficent ways of doing this
mnA:distinct each((>=),\:/:il),/:'{asc value min each(x@(=)distinct xrank[bckts;x])}peach db[il] //min interval and operator using buckets
mxA:distinct each((<=),\:/:il),/:'{asc value max each(x@(=)distinct xrank[bckts;x])}peach db[il] //max interval and operator using buckets
pairs:{2 3#x}each/:{(mnA@x) cross (mxA@x)}each (til count mxA); //interval pairs
idx:{{?[db;x;();`i]}each x}each pairs; //calculate index for each pair value
c:({where not 0=x}each({count each x}each idx));idx:idx@'c;pairs:pairs@'c; //only keep good indices
c:where not 0=(count each idx);idx:idx@c;pairs:pairs@c;badil:il[(til count il)except c];il:il@c; //![`db;();0b;badil] if it didn't have an idx- get rid of it. This removes bad variables
show "begin fit calc";show .z.Z;fit:{{getfit x}peach x}@/:idx;show .z.Z;show "end fit calc"; //calculate fitness
a:raze {x#y}'[count each pairs;til count pairs];v:raze iasc each pairs;
sm:`FIT xdesc (+) `av`FIT`cntbi`src!(enlist each av:{{x,y}'[x;y]}'[a;raze v];raze fit;count each raze idx;(count (raze fit))#`init);memclr@/:(`a`v`av);
mxcnt:count each pairs;show "starting loop";


//evaluate fitness for a given set of a and v
dofit:{[av;src]
 chk:distinct asc sm[`av];av:av[where not (asc av) in chk]; //don't run it again
 bi:(inter/)peach({{idx[x[0]]@x[1]}each x} each av); //find intersections
 gfit:{getfit x}peach bi;`FIT xdesc (+) `av`FIT`cntbi`src!(av;gfit;count each bi;(count gfit)#src)};

//build a random generation 
randgen:{[rndsize]
 a:{asc (neg x)?count pairs}each (1+rndsize?complx); //intial attribute population: pure random
 v:raze each{{1?x}each count each pairs[x]}each a; //intial intervals for the chosen attributes (family): pure random
 av:{{x,y}'[x;y]}'[a;v];dofit[av;`rand]}; //join the attributes and values together, update sm

//crossing children: cross good children
crssgen:{[crossover]
 t:gettop50[];R:til count t;lR:crossover?R;rR:crossover?R; //get the top 50% of the solutions- 
 c:(til crossover);c:c except (where lR=rR);lR:lR[c];rR:rR[c]; //cross them
 cnta:count each t[`av];rndlr:raze {1?x}each cnta[lR];rndrr:raze {1?x}each cnta[rR];
 avlr:{[x;y;z;w]x[z]:y[w];x}'[t[`av][lR];t[`av][rR];rndlr;rndrr];
 avrr:{[x;y;z;w]x[z]:y[w];x}'[t[`av][rR];t[`av][lR];rndrr;rndlr];(uj/){dofit[x;`crss]}each(avlr;avrr)};

//shifting children: randomly move in a direction 
shftgen:{[shftsize]
 t:(shftsize)#gettop50[];
 cnta:count each t[`av];
 avsu:{[x;y]z:(1?y);x[z]:x[z]:enlist ((raze x[z])[0],min((raze x[z])[1]+last sft[];mxcnt@(raze x[z])0));x}'[t[`av];cnta];
 avsd:{[x;y]z:(1?y);x[z]:x[z]:enlist ((raze x[z])[0],max((raze x[z])[1]-last sft[];0));x}'[t[`av];cnta];(uj/){dofit[x;`shift]}each(avsd;avsu)};

//joining children: join together good children: make larger solutions
joingen:{[joinsize]
 t:gettop50[];R:til count t;lR:joinsize?R;rR:joinsize?R;
 c:(til joinsize);c:c except (where lR=rR);lR:lR[c];rR:rR[c];
 av:{x,y}'[t[`av]@lR;t[`av]@rR];dofit[av;`join]};

//mutation: 
mutegen:{[mutesize]
	gs::exec av from (select avg FIT by av from raze flip each 0!sm) where 9=xrank[10;FIT]; //take top quartile of best singles
	t::mutesize?exec av from sm where 3=xrank[4;FIT],(count each av)>1; //setup our pool
	m::{(count x)?2}each t; //bool vector at rand: if 1b then we're switching it
	pgs::{x?gs}each(count each where each m); //pool of good solutions
	"b"$m;kept::{t[x] where not m[x]}each til count t; //switch around
	av::distinct {kept[x],pgs[x]}each til count kept;dofit[av;`mute]}

//recessive: using joins: It the system is stuck, recessives pulls from the bottom
recsgen:{[recssize]
 rs:recssize*(0>=(last exec deltas maxFIT from select max maxFIT by reverse gen from status)); //if we're not getting better, try recessives
 t:getbot50[];R:til count t;lR:rs?R;rR:rs?R;
 c:(til joinsize);c:c except (where lR=rR);lR:lR[c];rR:rR[c];
 av:{x,y}'[t[`av]@lR;t[`av]@rR];
 sm::select from sm where 1<xrank[10;FIT];
 dofit[av;`recs]};

//elites (top 10%): using crss
elitgen:{[elitesize]
 t:gettop25[];R:til count t;lR:crossover?R;rR:crossover?R;
 c:(til crossover);c:c except (where lR=rR);lR:lR[c];rR:rR[c];
 cnta:count each t[`av];rndlr:raze {1?x}each cnta[lR];rndrr:raze {1?x}each cnta[rR];
 avlr:{[x;y;z;w]x[z]:y[w];x}'[t[`av][lR];t[`av][rR];rndlr;rndrr];
 avrr:{[x;y;z;w]x[z]:y[w];x}'[t[`av][rR];t[`av][lR];rndrr;rndlr];(uj/){dofit[x;`elite]}each(avlr;avrr)};

//run all systems in || use \s 4 for 4 core machine.
while[0<gen;
	show gen;show .z.Z;
	status,::0!select gen:gen,cnt:count i,maxFIT:max FIT,avgFIT:avg FIT by src from sm;
	{sm::keepNdis[2;(sm,value x)]}each("randgen[rndsize]";"shftgen[shftsize]";"joingen[joinsize]";"crssgen[crossover]";"elitgen[elitesize]";"recsgen[recssize]");
	show select distinct maxFIT by src from status;gen-::1;show .z.Z;];

SOLUTIONS:`FIT xdesc (update Rules:indx2eng each av from (select av,FIT,cntbi from sm where cntbi>0,FIT>0));
show select Rules,FIT from SOLUTIONS
\
