// Global Kraft overlap-trie dual for a complete n=12 selection.
// All trail cut phases share a single choice on BOTH sides. Overlaps at depth
// min_key..8 are matched by trie key and priced with the same dual variable.
// Smaller overlaps are optimistically assigned min_key-1 even if unavailable.
// Therefore the bound is VALID for intact, weight-3 cuts only. A selection may
// be rejected for that model if its lower bound exceeds the target; do NOT use
// this to reject unrestricted weight-2 or split-trail arrangements.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <string>
#include <tuple>
#include <vector>
using namespace std;
struct Port{uint32_t off;uint64_t head;};
struct Trail{uint32_t first,count;};
struct KeyTrail{uint32_t key,tid;bool operator<(const KeyTrail&b)const{return tie(key,tid)<tie(b.key,b.tid);}};
struct Node{uint32_t key;int32_t pmin=-1,pmax=-1,smin=-1,smax=-1;};
struct State{uint32_t pre,suf;bool cin,cout;};
struct Level{int k;vector<Node> nodes;vector<State> st;vector<double> theta;vector<int32_t> grad;uint64_t cin=0,cout=0;};
struct Pick{int inlev=-1,outlev=-1;uint32_t ink=0,outk=0;};
static void fail(string s){throw runtime_error(s);}
static vector<Trail> load_trails(string path,uint64_t&total){
 ifstream f(path);if(!f)fail("cannot read: "+path);string hdr;getline(f,hdr);vector<Trail> t;
 uint32_t id,fi,np;uint64_t start,length;
 while(f>>id>>start>>length>>fi>>np){if(id!=t.size()||fi!=total||!np)fail("invalid trail index");t.push_back({fi,np});total+=np;}return t;
}
static vector<Port> load_ports(string path,uint64_t N){
 ifstream f(path,ios::binary|ios::ate);if(!f)fail("cannot read "+path);
 if(f.tellg()!=streamoff(N*12))fail("port binary length mismatch");f.seekg(0);
 vector<Port> ret(N);for(auto&p:ret){f.read((char*)&p.off,4);f.read((char*)&p.head,8);if(!f)fail("incomplete port file");for(int j=0;j<9;j++)if(((p.head>>(j*4))&15)>=12)fail("invalid symbol");}return ret;
}
static Level make_level(int k,const vector<Port>&ports,const vector<Trail>&trails){
 const uint64_t N=ports.size();Level l;l.k=k;l.st.resize(N);
 const uint32_t mask=(uint32_t)((1ULL<<(4*k))-1);
 vector<uint32_t> pre(N),suf(N);vector<uint32_t> keys;keys.reserve(N*2);
 for(uint32_t i=0;i<N;i++){
  pre[i]=uint32_t(ports[i].head>>(4*(9-k)));suf[i]=uint32_t(ports[i].head)&mask;
  keys.push_back(pre[i]);keys.push_back(suf[i]);
 }
 sort(keys.begin(),keys.end());keys.erase(unique(keys.begin(),keys.end()),keys.end());
 l.nodes.resize(keys.size());for(uint32_t j=0;j<keys.size();j++)l.nodes[j].key=keys[j];
 // Build both roles of the global connector trie at radix level k.
 // Each node stores the extreme source/destination trail IDs; this detects
 // an exact legal match on SOME DIFFERENT trail, not an internal self join.
 auto add=[&](const vector<uint32_t>&codes,bool isPre){
  vector<KeyTrail> pairs;pairs.reserve(N);
  for(uint32_t t=0;t<trails.size();t++)for(uint32_t i=trails[t].first;i<trails[t].first+trails[t].count;i++)pairs.push_back({codes[i],t});
  sort(pairs.begin(),pairs.end());
  for(size_t i=0;i<pairs.size();){size_t j=i+1;int32_t mn=pairs[i].tid,mx=mn;
   while(j<pairs.size()&&pairs[j].key==pairs[i].key){mn=min(mn,(int32_t)pairs[j].tid);mx=max(mx,(int32_t)pairs[j].tid);j++;}
   uint32_t ix=lower_bound(keys.begin(),keys.end(),pairs[i].key)-keys.begin();
   if(isPre){l.nodes[ix].pmin=mn;l.nodes[ix].pmax=mx;}
   else{l.nodes[ix].smin=mn;l.nodes[ix].smax=mx;}i=j;
  }
 };
 add(pre,true);add(suf,false);
 for(uint32_t t=0;t<trails.size();t++)for(uint32_t i=trails[t].first;i<trails[t].first+trails[t].count;i++){
  uint32_t a=lower_bound(keys.begin(),keys.end(),pre[i])-keys.begin();
  uint32_t b=lower_bound(keys.begin(),keys.end(),suf[i])-keys.begin();
  auto &na=l.nodes[a],&nb=l.nodes[b];
  bool inc=na.smin>=0&&(na.smin!=(int32_t)t||na.smax!=(int32_t)t);
  bool out=nb.pmin>=0&&(nb.pmin!=(int32_t)t||nb.pmax!=(int32_t)t);
  l.st[i]={a,b,inc,out};l.cin+=inc;l.cout+=out;
 }
 l.theta.resize(keys.size(),0.0);l.grad.resize(keys.size(),0);
 cerr<<"  trie depth="<<k<<" leaves="<<keys.size()<<" matched_entry_ports="<<l.cin<<" matched_exit_ports="<<l.cout<<"\n";
 return l;
}
int main(int argc,char**argv){
 try{
  if(argc<4){cerr<<"usage: global_trie_multilevel PREFIX CHARGE OUTPUT.json [min_key=7] [iterations=80] [step=0.04] [target=522736428]\n";return 2;}
  string prefix=argv[1],output=argv[3];int64_t Q=stoll(argv[2]);
  int min_key=argc>4?stoi(argv[4]):7;int rounds=argc>5?stoi(argv[5]):80;
  double step0=argc>6?stod(argv[6]):0.04;int64_t target=argc>7?stoll(argv[7]):522736428;
  if(min_key<1||min_key>8||rounds<0||step0<0)fail("bad parameters");
  uint64_t nports=0;auto trails=load_trails(prefix+".trails.tsv",nports);
  auto ports=load_ports(prefix+".ports.bin",nports);uint32_t T=trails.size();
  cerr<<"GLOBAL TRIE trails="<<T<<" ports="<<nports<<"\n";
  vector<Level> levels;levels.reserve(9-min_key);
  for(int k=min_key;k<=8;k++)levels.push_back(make_level(k,ports,trails));
  ports.clear();ports.shrink_to_fit();
  // Optional resumable dual prices; a run can cheaply tighten a prior bound.
  double previousBest=numeric_limits<double>::infinity();
  auto hash_keys=[](const Level&l){uint64_t h=1469598103934665603ULL;for(const auto&node:l.nodes){h^=node.key;h*=1099511628211ULL;}return h;};
  if(argc>8 && string(argv[8])!="-"){
   ifstream chk(argv[8],ios::binary);if(!chk)fail("cannot read checkpoint");
   uint64_t magic;int32_t mk,nl;
   chk.read((char*)&magic,8);chk.read((char*)&mk,4);chk.read((char*)&nl,4);
   chk.read((char*)&previousBest,8);
   if(magic!=0x4b52414654524e31ULL || mk!=min_key || nl!=(int)levels.size())fail("checkpoint header mismatch");
   for(auto &lev:levels){uint64_t n,hash;chk.read((char*)&n,8);chk.read((char*)&hash,8);
    if(n!=lev.nodes.size()||hash!=hash_keys(lev))fail("checkpoint trie mismatch");
    chk.read((char*)lev.theta.data(),n*sizeof(double));if(!chk)fail("truncated checkpoint");
   }
   cerr<<"  loaded checkpoint: best previous U="<<previousBest<<"\n";
  }
  vector<Pick> picked(T);vector<double> dualHist;dualHist.reserve(rounds+1);
  double best=previousBest;int bestiter=-1;
  // The convex global bound prices all key-specific connector usage.
  // Each phase picks exactly one incoming and one outgoing length, but both
  // must share the SAME phase, which is crucial for monodromy compatibility.
  for(int iter=0;iter<=rounds;iter++){
   double upper=0.0;int num8=0;
   for(uint32_t t=0;t<T;t++){
    double bestPhase=-1e70;Pick bestPick;
    auto tr=trails[t];
    for(uint32_t i=tr.first;i<tr.first+tr.count;i++){
     double in=.5*(min_key-1),out=in;Pick p;
     for(int z=0;z<levels.size();z++){
      const auto &l=levels[z];const auto &s=l.st[i];double length=.5*l.k;
      if(s.cin && length-l.theta[s.pre]>in){in=length-l.theta[s.pre];p.inlev=z;p.ink=s.pre;}
      if(s.cout&&length+l.theta[s.suf]>out){out=length+l.theta[s.suf];p.outlev=z;p.outk=s.suf;}
     }
     double score=in+out;
     if(score>bestPhase+1e-11){bestPhase=score;bestPick=p;}
    }
    upper+=bestPhase;picked[t]=bestPick;
    if(bestPick.inlev>=0&&levels[bestPick.inlev].k==8)num8++;
    if(bestPick.outlev>=0&&levels[bestPick.outlev].k==8)num8++;
   }
   if(upper<best){best=upper;bestiter=iter;}
   dualHist.push_back(upper);
   if(iter==rounds)break;
   for(const auto&p:picked){if(p.inlev>=0)levels[p.inlev].grad[p.ink]--;
                             if(p.outlev>=0)levels[p.outlev].grad[p.outk]++;}
   double eta=step0/sqrt(1.0+0.2*iter);
   for(auto &l:levels)for(uint32_t i=0;i<l.grad.size();i++)if(l.grad[i]){l.theta[i]-=eta*l.grad[i];l.grad[i]=0;}
   if(iter%20==0||iter==rounds-1)cerr<<"  iteration="<<iter<<" overlap_UB="<<fixed<<setprecision(4)<<upper<<" best="<<best<<" eight_roles="<<num8<<"\n";
  }
  // The floor is certified: each real matched overlap of length k has equal
  // outgoing and incoming trie key; its dual potentials cancel. All omitted
  // k < min_key are overestimated as min_key-1, so true overlap <= dual.
  // Closing the path with a DUMMY zero-overlap edge balances the endpoint roles.
  int64_t U=(int64_t)ceil(best+1e-5);
  int64_t J=9LL*T-U, F3=522547200,L=F3+Q+J;
  ofstream f(output);if(!f)fail("cannot write output");
  f<<"{\n\"scope\":\"one intact weight-3 cut per trail (NOT weight-2 or trail splits)\",\n";
  f<<"\"certified_for_unrestricted_search\":false,\n";
  f<<"\"trails\":"<<T<<",\"ports\":"<<nports<<",\"charge\":"<<Q<<",\"min_key\":"<<min_key<<",\n";
  f<<"\"trie_levels\":[";for(size_t i=0;i<levels.size();i++){
    auto &lev=levels[i];if(i)f<<",";
    f<<"{\"depth\":"<<lev.k<<",\"nodes\":"<<lev.nodes.size()<<",\"incoming_available\":"<<lev.cin<<",\"outgoing_available\":"<<lev.cout<<"}";
  }f<<"],\n";
  f<<"\"dual_overlap_upper_raw\":"<<setprecision(12)<<best<<",\"certified_overlap_upper\":"<<U<<",\n";
  f<<"\"joining_cost_lower_bound\":"<<J<<",\"length_lower_bound\":"<<L<<",\"target_to_beat\":"<<target<<",\n";
  f<<"\"certified_reject_restricted\":"<<(L>=target?"true":"false")<<",\n";
  f<<"\"iterations\":"<<rounds<<",\"best_iteration\":"<<bestiter<<",\"dual_history\":[";
  for(int i=0;i<dualHist.size();i++){if(i)f<<",";f<<setprecision(9)<<dualHist[i];}f<<"]\n}\n";
  if(argc>9 && string(argv[9])!="-"){
   ofstream chk(argv[9],ios::binary|ios::trunc);if(!chk)fail("cannot save checkpoint");
   uint64_t magic=0x4b52414654524e31ULL;int32_t mk=min_key,nl=levels.size();
   chk.write((char*)&magic,8);chk.write((char*)&mk,4);chk.write((char*)&nl,4);
   chk.write((char*)&best,8);
   for(auto &lev:levels){uint64_t n=lev.nodes.size(),hash=hash_keys(lev);
    chk.write((char*)&n,8);chk.write((char*)&hash,8);
    chk.write((char*)lev.theta.data(),n*sizeof(double));
   }
  }
  cout<<"GLOBAL_TRIE trails="<<T<<" Q="<<Q<<" level="<<min_key<<"..8 U<="<<U<<" J>="<<J<<" L>="<<L<<" restricted_reject="<<(L>=target?"yes":"no")<<"\n";
 }catch(exception&e){cerr<<"ERROR: "<<e.what()<<"\n";return 1;}
}
