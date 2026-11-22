// Selection-derived global-port generator with no 522-million-symbol literal intermediate.
#include <bits/stdc++.h>
using namespace std;
struct Slice{uint64_t head,tail,b;uint8_t d,c;};
static inline uint64_t pack(const uint8_t *a,int n){uint64_t x=0;for(int i=0;i<n;i++)x=(x<<4)|a[i];return x;}
static inline int digit(char c){return c<='9'?c-'0':c-'A'+10;}
static inline char sym(int i){return i<10?'0'+i:'A'+i-10;}
static inline void rot(const uint8_t*a,int n,int r,uint8_t*b){for(int i=0;i<n;i++)b[i]=a[(i+r)%n];}
uint32_t emit(const Slice&s,FILE*f){
 uint8_t b[11];auto x=s.b;for(int i=10;i>=0;i--){b[i]=x&15;x>>=4;}
 uint8_t bb[22];memcpy(bb,b,11);memcpy(bb+11,b,11);
 char q[160];int k=0;for(int i=0;i<11;i++)q[k++]=sym(b[i]);q[k++]=sym(s.d);for(int i=0;i<11;i++)q[k++]=sym(b[i]);
 for(int j=0;j<s.c-1;j++){q[k++]=sym(bb[j]);q[k++]=sym(s.d);for(int t=j+1;t<j+12;t++)q[k++]=sym(bb[t]);}
 assert(k>=9);k-=9;if(f)fwrite(q,1,k,f);return k;
}
int main(int argc,char**argv){
 if(argc!=3){fprintf(stderr,"usage generate_ports_only full.selection outprefix\n");return 2;}
 ifstream fi(argv[1]);if(!fi){cerr<<"not found\n";return 3;}
 vector<Slice> sl;sl.reserve(4000000);
 string a,v;uint64_t classes=0,charge=0,det=0;
 while(fi>>a>>v){if(a[0]=='#'){string rest;getline(fi,rest);continue;}if(a.size()!=10){cerr<<"bad row "<<a<<"\n";return 3;}
  uint8_t x[10];for(int i=0;i<10;i++)x[i]=digit(a[i]);
  int vis =v=="F"?10:v=="S"?8:v=="D"?0:stoi(v);classes++;charge+=(vis?10-vis:0);det+=(vis==0);
  auto add=[&](const uint8_t*b,int d,int c){uint8_t r[11];rot(b,11,(c+1)%11,r);sl.push_back(Slice{pack(b,9),pack(r,9),pack(b,11),(uint8_t)d,(uint8_t)c});};
  if(vis){for(int j=0;j<10;j++){uint8_t b[11];for(int i=0;i<j;i++)b[i]=x[i];b[j]=11;for(int i=j;i<10;i++)b[i+1]=x[i];add(b,10,vis+(j<vis));}}
  for(int j=vis;j<10;j++){uint8_t b[11];for(int i=0;i<10;i++)b[i]=x[(i+j)%10];b[10]=10;add(b,11,11);}
 }
 cerr<<"parsed classes "<<classes<<" Q="<<charge<<" detached="<<det<<" ports="<<sl.size()<<"\n";
 if(classes!=362880 || sl.size()!=3628800+charge){cerr<<"unexpected size\n";return 3;}
 unordered_map<uint64_t,uint32_t> map;map.max_load_factor(.7);map.reserve(sl.size()+10000);
 for(uint32_t i=0;i<sl.size();i++){if(!map.emplace(sl[i].head,i).second){cerr<<"duplicate head\n";return 4;}}
 vector<uint32_t> next(sl.size());vector<uint8_t> indeg(sl.size());
 for(uint32_t i=0;i<sl.size();i++){auto it=map.find(sl[i].tail);if(it==map.end()){cerr<<"missing tail\n";return 4;}next[i]=it->second;indeg[it->second]++;}
 for(auto x:indeg)if(x!=1){cerr<<"wrong indeg\n";return 4;}
 string prefix=argv[2];FILE*fw=nullptr;FILE*fp=fopen((prefix+".ports.bin").c_str(),"wb");ofstream ft(prefix+".trails.tsv");ft<<"trail\tstart\tlength\tfirstport\tports\n";
 if(!fp||!ft){cerr<<"cannot create files\n";return 6;}
 vector<uint8_t> visited(sl.size());uint64_t allbytes=0,portseen=0;uint32_t tid=0;uint64_t maxtrail=0;
 for(uint32_t i=0;i<sl.size();i++)if(!visited[i]){
  uint64_t st=allbytes,firstport=portseen;uint32_t v=i,cnt=0;do{
   if(visited[v]){cerr<<"not a cycle\n";return 5;}visited[v]=1;
   uint32_t offset=allbytes-st;uint64_t record=sl[v].head;
   fwrite(&offset,4,1,fp);fwrite(&record,8,1,fp);
   allbytes+=emit(sl[v],fw);portseen++;cnt++;v=next[v];
  }while(v!=i);
  ft<<tid<<'\t'<<st<<'\t'<<allbytes-st<<'\t'<<firstport<<'\t'<<cnt<<'\n';tid++;
  maxtrail=max(maxtrail,allbytes-st);
  if(tid%500==0)cerr<<"trail "<<tid<<" letters="<<allbytes<<"\n";
 }
 fclose(fp);ft.close();
 cerr<<"FINISHED trails="<<tid<<" words="<<allbytes<<" maxtrail="<<maxtrail<<" ports="<<portseen<<" Q="<<charge<<"\n";
 if(portseen!=sl.size() || tid==0) return 7;
}
