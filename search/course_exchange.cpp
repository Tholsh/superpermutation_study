// Reconstruct a witness in the exact cyclic-course basis before optimizing it.
// No DSU module contiguity or module order is assumed.
#define COUPLED_CYCLE_LIBRARY
#include "../boundary-spectral-n11-20261004/coupled_cycle_search.cpp"
#include <functional>

static uint32_t courseRank(const std::string& w,size_t p) {
    static constexpr uint32_t f[]={1,1,2,6,24,120,720,5040,40320,362880,3628800,39916800};
    unsigned unused=2047;uint32_t r=0;for(int j=0;j<11;++j){unsigned bit=1u<<alphabet.find(w[p+j]);if(!(unused&bit))return UINT32_MAX;r+=__builtin_popcount(unused&(bit-1))*f[10-j];unused^=bit;}return r;
}
struct LiteralCourse {int root;std::vector<int> rows;std::string period;std::vector<size_t> assigned,cheapCuts;std::unordered_map<uint32_t,std::vector<uint32_t>> extraCopies;std::vector<size_t> allLiteralCuts;};
struct CourseRun {int colour;size_t first,last;};
static bool occupationSlack=false;
static uint64_t frameBits(const std::string&s,size_t start){uint64_t v=0;for(int k=0;k<11;++k)v=(v<<4)|alphabet.find(s[(start+k)%s.size()]);return v;}
static int frameOverlap(uint64_t a,uint64_t b){for(int k=11;k>0;--k)if((a&((uint64_t(1)<<(4*k))-1))==(b>>(4*(11-k))))return k;return 0;}
static uint32_t rankFrameBits(uint64_t frame){static constexpr uint32_t f[]={1,1,2,6,24,120,720,5040,40320,362880,3628800,39916800};unsigned unused=2047;uint32_t value=0;
    for(int k=0;k<11;++k){unsigned bit=1u<<((frame>>(4*(10-k)))&15);require(bool(unused&bit),"permutation frame rank");value+=__builtin_popcount(unused&(bit-1))*f[10-k];unused^=bit;}return value;}
static std::pair<int,uint64_t> occupationEnd(const LiteralCourse&q,size_t cut,size_t assignedIndex,int ordinaryPad,uint64_t ordinaryLast){
    if(!occupationSlack||q.extraCopies.empty())return {ordinaryPad,ordinaryLast};
    size_t cursor=assignedIndex?assignedIndex-1:q.assigned.size()-1,replacementMaximum=0;
    for(size_t steps=0;steps<q.assigned.size();++steps){size_t at=q.assigned[cursor],rotated=(at+q.period.size()-cut)%q.period.size(),earliest=rotated;
        auto id=rankFrameBits(frameBits(q.period,at));auto found=q.extraCopies.find(id);if(found!=q.extraCopies.end())for(size_t other:found->second)earliest=std::min(earliest,(other+q.period.size()-cut)%q.period.size());
        if(earliest==rotated){size_t lastRequired=std::max(rotated,replacementMaximum);int64_t pad=int64_t(lastRequired)+11-int64_t(q.period.size());require(pad>=-32&&pad<=10,"occupation slack packed-price guard");return {int(pad),frameBits(q.period,cut+lastRequired)};}
        replacementMaximum=std::max(replacementMaximum,earliest);cursor=cursor?cursor-1:q.assigned.size()-1;
    }
    throw std::runtime_error("occupation backwards stopping invariant");
}
struct CutChoice {int price=30000,pad=0;size_t cut=0;};
template<class Callback> static void eachOpening(const LiteralCourse&q,bool allPhases,Callback visit) {
    const auto&cuts=allPhases?(q.allLiteralCuts.empty()?q.assigned:q.allLiteralCuts):q.cheapCuts;size_t position=0;
    uint64_t current=frameBits(q.period,0),mask=(uint64_t(1)<<44)-1;
    size_t assignedIndex=0;
    for(size_t cut:cuts){while(position<cut){++position;current=((current<<4)&mask)|alphabet.find(q.period[(position+10)%q.period.size()]);}
        while(assignedIndex<q.assigned.size()&&q.assigned[assignedIndex]<cut)++assignedIndex;
        size_t before=assignedIndex?q.assigned[assignedIndex-1]:q.assigned.back();
        int pad=11-int((cut+q.period.size()-before)%q.period.size());auto end=occupationEnd(q,cut,assignedIndex,pad,frameBits(q.period,before));visit(current,end.second,end.first,cut);}
}
static CutChoice queryOpening(const LiteralCourse&q,uint64_t left,uint64_t right,bool hasLeft,bool hasRight,bool allPhases) {
    CutChoice best;eachOpening(q,allPhases,[&](uint64_t first,uint64_t last,int pad,size_t cut){int price=pad-(hasLeft?frameOverlap(left,first):0)-(hasRight?frameOverlap(last,right):0);if(price<best.price)best={price,pad,cut};});return best;
}
static void occupationEndControls(const std::vector<LiteralCourse>&courses,const std::vector<uint16_t>&owner){
    std::vector<uint64_t>seen((owner.size()+63)/64);int controls=0,colours=0;
    for(size_t c=0;c<courses.size()&&colours<12;++c){const auto&q=courses[c];if(q.extraCopies.empty())continue;++colours;
        std::vector<size_t>cuts{0,q.assigned.back(),q.extraCopies.begin()->second.front()};
        for(size_t cut:cuts){size_t index=std::lower_bound(q.assigned.begin(),q.assigned.end(),cut)-q.assigned.begin();size_t before=index?q.assigned[index-1]:q.assigned.back();int ordinary=11-int((cut+q.period.size()-before)%q.period.size());auto result=occupationEnd(q,cut,index,ordinary,frameBits(q.period,before));
            auto literal=cyclicText(q.period,cut,q.period.size()+11);std::fill(seen.begin(),seen.end(),0);size_t distinct=0,lastFirst=0;
            for(size_t p=0;p+11<=literal.size();++p){auto rank=courseRank(literal,p);if(rank==UINT32_MAX||owner[rank]!=c)continue;auto&bucket=seen[rank/64];uint64_t bit=uint64_t(1)<<(rank%64);if(!(bucket&bit)){bucket|=bit;++distinct;lastFirst=p;}}
            require(distinct==q.assigned.size(),"occupation end brute-force assigned coverage");require(int64_t(lastFirst)+11==int64_t(q.period.size())+result.first,"occupation end exact shortest-prefix oracle");require(frameBits(literal,lastFirst)==result.second,"occupation end literal terminal frame");++controls;}
    }
    std::cout<<"occupation_end_controls="<<controls<<" exact shortest prefixes passed"<<std::endl;
}
struct SwapResult {int saving=0;size_t i=0,j=0;CutChoice atI,atJ;uint64_t ports=0,strongUpdates=0,pairs=0,pruned=0,fallbackQueries=0;};
static SwapResult phaseSwaps(const std::vector<LiteralCourse>&courses,const std::vector<int>&order,const std::vector<std::string>&pieces,bool allPhases,const std::filesystem::path&out) {
    const size_t n=order.size();require(n==courses.size()&&n<UINT16_MAX,"once-only course exchange inventory");
    std::vector<uint64_t> left(n),right(n);std::vector<int> oldPrice(n),minPad(courses.size(),11);std::vector<int8_t> strong(n*courses.size(),120);
    std::unordered_map<uint64_t,std::vector<uint16_t>> leftKeys,rightKeys;leftKeys.reserve(n*9);rightKeys.reserve(n*9);
    auto key=[](uint64_t frame,int len,bool suffix){return (uint64_t(1)<<(4*len))|(suffix?(frame&((uint64_t(1)<<(4*len))-1)):(frame>>(4*(11-len))));};
    for(size_t i=0;i<n;++i){if(i)left[i]=frameBits(pieces[i-1],pieces[i-1].size()-11);if(i+1<n)right[i]=frameBits(pieces[i+1],0);
        oldPrice[i]=int(pieces[i].size()-courses[order[i]].period.size())-(i?frameOverlap(left[i],frameBits(pieces[i],0)):0)-(i+1<n?frameOverlap(frameBits(pieces[i],pieces[i].size()-11),right[i]):0);
        for(int k=4;k<=11;++k){if(i)leftKeys[key(left[i],k,true)].push_back(uint16_t(i));if(i+1<n)rightKeys[key(right[i],k,false)].push_back(uint16_t(i));}}
    SwapResult result;auto started=std::chrono::steady_clock::now();
    for(size_t c=0;c<courses.size();++c){eachOpening(courses[c],allPhases,[&](uint64_t first,uint64_t last,int pad,size_t){++result.ports;minPad[c]=std::min(minPad[c],pad);
            auto update=[&](const std::vector<uint16_t>&indices){for(auto i:indices){int price=pad-(i?frameOverlap(left[i],first):0)-(i+1<n?frameOverlap(last,right[i]):0);auto&value=strong[size_t(i)*courses.size()+c];value=int8_t(std::min(int(value),price));++result.strongUpdates;}};
            for(int k=4;k<=11;++k){auto a=leftKeys.find(key(first,k,false));if(a!=leftKeys.end())update(a->second);auto b=rightKeys.find(key(last,k,true));if(b!=rightKeys.end())update(b->second);}});
        if(c%400==0)std::cout<<"phase_swap_ports course="<<c<<'/'<<courses.size()<<" all_phases="<<allPhases<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<std::endl;}
    // If neither attachment overlaps by >=4, its total overlap is <=6.
    // This is an exact optimistic bound, not a learned rejection rule.
    auto weakBound=[&](size_t context,int c){return minPad[c]-3*((context>0)+(context+1<n));};
    std::mt19937 oracleRandom(410043);for(int t=0;t<1000;++t){size_t i=oracleRandom()%n;int c=oracleRandom()%courses.size();int best=queryOpening(courses[c],left[i],right[i],i>0,i+1<n,allPhases).price;int s=strong[i*courses.size()+c],w=weakBound(i,c);require(std::min(s,w)<=best&&best<=s,"strong/weak bounds versus direct phase oracle");if(s<=w)require(best==s,"strong match certifies exact minimum");}
    for(size_t i=0;i<n;++i)for(size_t j=i+2;j<n;++j){++result.pairs;int ci=order[i],cj=order[j],a=strong[i*courses.size()+cj],b=strong[j*courses.size()+ci];int wa=weakBound(i,cj),wb=weakBound(j,ci),old=oldPrice[i]+oldPrice[j];
        if(std::min(a,wa)+std::min(b,wb)>=old-result.saving){++result.pruned;continue;}
        CutChoice qa,qb;if(a<=wa)qa.price=a;else{qa=queryOpening(courses[cj],left[i],right[i],i>0,i+1<n,allPhases);++result.fallbackQueries;}
        if(b<=wb)qb.price=b;else{qb=queryOpening(courses[ci],left[j],right[j],j>0,j+1<n,allPhases);++result.fallbackQueries;}
        int gain=old-qa.price-qb.price;if(gain>result.saving){result.saving=gain;result.i=i;result.j=j;std::cout<<"phase_swap_saving="<<gain<<" positions="<<i<<','<<j<<std::endl;}}
    if(result.saving>0){int ci=order[result.i],cj=order[result.j];result.atI=queryOpening(courses[cj],left[result.i],right[result.i],result.i>0,result.i+1<n,allPhases);result.atJ=queryOpening(courses[ci],left[result.j],right[result.j],result.j>0,result.j+1<n,allPhases);require(oldPrice[result.i]+oldPrice[result.j]-result.atI.price-result.atJ.price==result.saving,"exact swap reconstruction prices");}
    std::ofstream log(out/(allPhases?"all-phase-swaps.json":"constituent-phase-swaps.json"));log<<"{\"all_phases\":"<<(allPhases?"true":"false")<<",\"ports\":"<<result.ports<<",\"strong_match_updates\":"<<result.strongUpdates<<",\"nonadjacent_pairs\":"<<result.pairs<<",\"exact_bound_pruned\":"<<result.pruned<<",\"fallback_full_phase_queries\":"<<result.fallbackQueries<<",\"saving\":"<<result.saving<<",\"positions\":["<<result.i<<','<<result.j<<"],\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<"}\n";return result;
}
static void phaseBoundControls(){
    std::mt19937 random(410042);int checked=0;for(int t=0;t<1000;++t){std::string a="0123456789A",b=a,l=a,r=a;std::shuffle(a.begin(),a.end(),random);std::shuffle(b.begin(),b.end(),random);std::shuffle(l.begin(),l.end(),random);std::shuffle(r.begin(),r.end(),random);
        if(t%3==0)l=a;if(t%5==0)r=b;auto f=frameBits(a,0),z=frameBits(b,0),x=frameBits(l,0),y=frameBits(r,0);require(frameOverlap(x,f)==ov(l,a)&&frameOverlap(z,y)==ov(b,r),"packed literal overlap oracle");
        int alpha=frameOverlap(x,f),beta=frameOverlap(z,y),pad=8+t%3;if(alpha<4&&beta<4)require(pad-alpha-beta>=2,"weak attachment bound");++checked;}
    std::cout<<"phase_bound_controls="<<checked<<" passed"<<std::endl;
}
// Exact min-plus contraction of two phase families. Each prefix bucket is an
// outer-product interface: a left suffix activates precisely matching right
// prefixes. Keep the minimizing literal port, not merely its cost.
struct AdjPort {uint64_t first,last;uint32_t cut;int pad;};
struct AdjAnswer {int price=30000;AdjPort a{},b{};};
static uint64_t adjKey(uint64_t frame,int k,bool suffix){
    uint64_t mask=(uint64_t(1)<<(4*k))-1;
    return (uint64_t(1)<<(4*k))|(suffix?(frame&mask):(frame>>(4*(11-k))));
}
static AdjAnswer adjacentContract(const std::vector<AdjPort>&a,const std::vector<AdjPort>&b,
                                  uint64_t left,uint64_t right,bool hasLeft,bool hasRight){
    struct Entry {int price;uint32_t index;};
    std::unordered_map<uint64_t,Entry> prefix;prefix.reserve(b.size()*9);
    for(uint32_t j=0;j<b.size();++j){const auto&p=b[j];int base=p.pad-(hasRight?frameOverlap(p.last,right):0);
        for(int k=0;k<=11;++k){uint64_t key=adjKey(p.first,k,false);int price=base-k;
            auto [it,inserted]=prefix.emplace(key,Entry{price,j});
            if(!inserted&&price<it->second.price)it->second={price,j};}}
    AdjAnswer best;
    for(const auto&p:a){int base=p.pad-(hasLeft?frameOverlap(left,p.first):0);
        for(int k=0;k<=11;++k){auto it=prefix.find(adjKey(p.last,k,true));
            if(it!=prefix.end()&&base+it->second.price<best.price)
                best={base+it->second.price,p,b[it->second.index]};}}
    require(best.price==best.a.pad+best.b.pad-(hasLeft?frameOverlap(left,best.a.first):0)
        -frameOverlap(best.a.last,best.b.first)-(hasRight?frameOverlap(best.b.last,right):0),"adjacent contraction literal replay");
    return best;
}
static void adjacentControls(){
    std::mt19937 random(410044);std::string symbols="0123456789A";
    for(int t=0;t<200;++t){std::vector<AdjPort>a,b;
        for(int j=0;j<17;++j){std::shuffle(symbols.begin(),symbols.end(),random);uint64_t first=frameBits(symbols,0);
            std::shuffle(symbols.begin(),symbols.end(),random);uint64_t last=frameBits(symbols,0);
            (j%2?a:b).push_back({first,last,uint32_t(j),int(random()%15)-4});}
        uint64_t left=a[random()%a.size()].first,right=b[random()%b.size()].last;bool hl=t%2,hr=t%3;
        int brute=30000;for(const auto&x:a)for(const auto&y:b)brute=std::min(brute,x.pad+y.pad
            -(hl?frameOverlap(left,x.first):0)-frameOverlap(x.last,y.first)-(hr?frameOverlap(y.last,right):0));
        require(adjacentContract(a,b,left,right,hl,hr).price==brute,"adjacent contraction exhaustive control");}
    std::cout<<"adjacent_bruteforce_controls=200 passed"<<std::endl;
}
static void adjacentSearch(const std::vector<LiteralCourse>&courses,const std::vector<int>&order,
    const std::vector<std::string>&pieces,const std::string&word,const std::filesystem::path&out,double seconds,bool global=false){
    adjacentControls();auto start=std::chrono::steady_clock::now();
    std::vector<std::vector<AdjPort>> ports(courses.size());uint64_t count=0;
    for(size_t c=0;c<courses.size();++c){eachOpening(courses[c],true,[&](uint64_t f,uint64_t l,int pad,size_t cut){
        ports[c].push_back({f,l,uint32_t(cut),pad});++count;});}
    std::cout<<"cached_all_phase_ports="<<count<<" payload_bytes="<<count*sizeof(AdjPort)<<std::endl;
    if(global){
        struct Entry {int cost;uint32_t index;};
        std::vector<std::vector<uint32_t>> parent(order.size());std::vector<int> previous;
        for(size_t layer=0;layer<order.size();++layer){const auto&current=ports[order[layer]];std::vector<int> next(current.size());
            if(layer==0){for(size_t j=0;j<current.size();++j)next[j]=current[j].pad;}
            else{const auto&before=ports[order[layer-1]];std::unordered_map<uint64_t,Entry> suffix;suffix.reserve(before.size()*9);
                for(uint32_t j=0;j<before.size();++j)for(int k=0;k<=11;++k){auto key=adjKey(before[j].last,k,true);int cost=previous[j]-k;
                    auto[it,inserted]=suffix.emplace(key,Entry{cost,j});if(!inserted&&cost<it->second.cost)it->second={cost,j};}
                parent[layer].resize(current.size());
                for(size_t j=0;j<current.size();++j){int best=INT_MAX;uint32_t winner=0;
                    for(int k=0;k<=11;++k){auto it=suffix.find(adjKey(current[j].first,k,false));if(it!=suffix.end()&&it->second.cost<best){best=it->second.cost;winner=it->second.index;}}
                    next[j]=best+current[j].pad;parent[layer][j]=winner;
                    require(next[j]==previous[winner]+current[j].pad-frameOverlap(before[winner].last,current[j].first),"global phase recurrence literal replay");}}
            previous=std::move(next);
            if(layer%100==0)std::cout<<"global_phase_layer="<<layer<<" states="<<current.size()<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
        }
        uint32_t at=uint32_t(std::min_element(previous.begin(),previous.end())-previous.begin());int optimal=previous[at];
        auto changed=pieces;std::ofstream schedule(out/"global-phase-schedule.jsonl");
        for(size_t layer=order.size();layer-->0;){const auto&p=ports[order[layer]][at];const auto&q=courses[order[layer]];
            changed[layer]=cyclicText(q.period,p.cut,q.period.size()+p.pad);
            schedule<<"{\"position\":"<<layer<<",\"course\":"<<q.root<<",\"cut\":"<<p.cut<<",\"pad\":"<<p.pad<<"}\n";
            if(layer)at=parent[layer][at];}
        auto candidate=joinedWord(changed);uint64_t bulk=0;for(const auto&q:courses)bulk+=q.period.size();
        require(int64_t(candidate.size())==int64_t(bulk)+optimal,"global phase telescoping cost");
        require(candidate.size()<=word.size(),"global incumbent feasible");
        std::ofstream f(out/("global-phase-n11-"+std::to_string(candidate.size())+".txt"),std::ios::binary);f<<candidate;require(bool(f),"global candidate output");
        std::ofstream report(out/"global-phase-summary.json");report<<"{\"original_length\":"<<word.size()<<",\"length\":"<<candidate.size()<<",\"saving\":"<<word.size()-candidate.size()<<",\"ports\":"<<count<<",\"layers\":"<<order.size()<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<",\"fixed_course_order\":true,\"independent_scan_required\":true}\n";
        std::cout<<"global_phase_candidate="<<candidate.size()<<" saving="<<word.size()-candidate.size()<<" independent_scan_required=1"<<std::endl;return;
    }
    std::ofstream trials(out/"adjacent-all-phase.jsonl");size_t tested=0;int gains=0;
    for(size_t i=0;i+1<order.size();++i){if(std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()>seconds)break;
        uint64_t left=i?frameBits(pieces[i-1],pieces[i-1].size()-11):0,right=i+2<pieces.size()?frameBits(pieces[i+2],0):0;
        bool hl=i>0,hr=i+2<pieces.size();int ca=order[i],cb=order[i+1];
        int old=int(pieces[i].size())-int(courses[ca].period.size())+int(pieces[i+1].size())-int(courses[cb].period.size())
            -(hl?frameOverlap(left,frameBits(pieces[i],0)):0)-frameOverlap(frameBits(pieces[i],pieces[i].size()-11),frameBits(pieces[i+1],0))
            -(hr?frameOverlap(frameBits(pieces[i+1],pieces[i+1].size()-11),right):0);
        auto ab=adjacentContract(ports[ca],ports[cb],left,right,hl,hr);
        require(ab.price<=old,"original adjacent pair remains feasible");
        auto ba=adjacentContract(ports[cb],ports[ca],left,right,hl,hr);bool reverse=ba.price<ab.price;
        const auto&best=reverse?ba:ab;int gain=old-best.price;++tested;
        trials<<"{\"position\":"<<i<<",\"old_price\":"<<old<<",\"same_order_price\":"<<ab.price<<",\"reverse_order_price\":"<<ba.price<<",\"saving\":"<<gain<<"}\n";trials.flush();
        if(gain>0){auto changed=pieces;int c1=reverse?cb:ca,c2=reverse?ca:cb;
            changed[i]=cyclicText(courses[c1].period,best.a.cut,courses[c1].period.size()+best.a.pad);
            changed[i+1]=cyclicText(courses[c2].period,best.b.cut,courses[c2].period.size()+best.b.pad);
            auto candidate=joinedWord(changed);require(int64_t(word.size())-int64_t(candidate.size())==gain,"adjacent global literal saving");
            std::ofstream f(out/("adjacent-n11-"+std::to_string(candidate.size())+".txt"),std::ios::binary);f<<candidate;require(bool(f),"adjacent candidate output");
            std::cout<<"candidate_length="<<candidate.size()<<" saving="<<gain<<" position="<<i<<" independent_scan_required=1"<<std::endl;++gains;break;}
        if(tested%50==0)std::cout<<"adjacent_pairs="<<tested<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
    }
    std::ofstream summary(out/"adjacent-summary.json");summary<<"{\"tested\":"<<tested<<",\"total_pairs\":"<<order.size()-1<<",\"gains\":"<<gains<<",\"ports\":"<<count<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<"}\n";
}
int main(int argc,char**argv)try{
    require(argc==7||argc==8,"usage: course_exchange ROWS CIRCLES WORD FRESH_OUT WINDOW_SIZE SECONDS [--pair-swaps|--occupation-swaps|--adjacent-all-phases|--global-all-phases]");bool swaps=argc==8;bool global=swaps&&std::string(argv[7])=="--global-all-phases";bool adjacent=swaps&&(global||std::string(argv[7])=="--adjacent-all-phases");occupationSlack=swaps&&(adjacent||std::string(argv[7])=="--occupation-swaps");require(!swaps||occupationSlack||std::string(argv[7])=="--pair-swaps","known exchange mode");int width=std::stoi(argv[5]);double seconds=std::stod(argv[6]);
    require(width>=2&&width<=8&&seconds>=0,"bounded course controls");std::filesystem::path out(argv[4]);require(!std::filesystem::exists(out),"fresh output");std::filesystem::create_directories(out);
    Model m;m.load(argv[1],argv[2]);std::map<int,std::vector<int>> courseRows;for(size_t r=0;r<m.payload.size();++r)courseRows[m.colour[r]].push_back(int(r));
    std::vector<LiteralCourse> courses;std::vector<uint16_t> owner(39916800,UINT16_MAX);std::vector<uint32_t> assignedOffset(39916800,UINT32_MAX);
    for(const auto&[root,rows]:courseRows){int c=int(courses.size());LiteralCourse q{root,rows,m.head[rows.front()],{},{} };int at=rows.front();size_t off=0;
        do{const auto&w=m.payload[at];int visible=int((w.size()-9)/12);for(int j=0;j<visible;++j){q.cheapCuts.push_back(off+12*j);for(int k=0;k<11;++k){size_t offset=off+12*j+k;auto rank=courseRank(w,12*j+k);require(rank<owner.size()&&owner[rank]==UINT16_MAX,"course occupation partition");owner[rank]=uint16_t(c);assignedOffset[rank]=uint32_t(offset);q.assigned.push_back(offset);}}
            q.period+=w.substr(8);off+=w.size()-8;at=m.next[at];}while(at!=rows.front());
        require(q.period.size()==off+8&&q.period.compare(off,8,q.period,0,8)==0,"literal periodic closure");q.period.resize(off);courses.push_back(std::move(q));}
    require(std::find(owner.begin(),owner.end(),UINT16_MAX)==owner.end(),"all S11 assigned");std::ifstream in(argv[3],std::ios::binary);require(bool(in),"word input");std::string word((std::istreambuf_iterator<char>(in)),{});if(!word.empty()&&word.back()=='\n')word.pop_back();for(char c:word)require(alphabet.find(c)<11,"word alphabet");
    if(occupationSlack){uint64_t extra=0,borrowed=0;for(size_t c=0;c<courses.size();++c){auto&q=courses[c];auto cyclic=q.period+q.period.substr(0,10);std::vector<size_t>extraCuts;for(size_t p=0;p<q.period.size();++p){auto id=courseRank(cyclic,p);if(id==UINT32_MAX)continue;if(owner[id]!=c){++borrowed;continue;}if(assignedOffset[id]!=p){q.extraCopies[id].push_back(uint32_t(p));extraCuts.push_back(p);++extra;}}
            if(!extraCuts.empty()){q.allLiteralCuts=q.assigned;q.allLiteralCuts.insert(q.allLiteralCuts.end(),extraCuts.begin(),extraCuts.end());std::sort(q.allLiteralCuts.begin(),q.allLiteralCuts.end());q.cheapCuts.insert(q.cheapCuts.end(),extraCuts.begin(),extraCuts.end());std::sort(q.cheapCuts.begin(),q.cheapCuts.end());}}
        std::cout<<"cyclic_extra_copies="<<extra<<" borrowed_other_course_windows="<<borrowed<<std::endl;std::ofstream extras(out/"cyclic-occupation.json");extras<<"{\"extra_copies_within_own_course\":"<<extra<<",\"other_course_windows\":"<<borrowed<<"}\n";occupationEndControls(courses,owner);}
    std::vector<CourseRun> runs;for(size_t p=0;p+11<=word.size();++p){auto rank=courseRank(word,p);if(rank==UINT32_MAX)continue;int c=owner[rank];if(runs.empty()||runs.back().colour!=c)runs.push_back({c,p,p});else runs.back().last=p;}
    std::vector<int> visits(courses.size());for(const auto&r:runs)++visits[r.colour];
    std::vector<std::string> pieces;std::ofstream log(out/"reconstruction.jsonl");int failures=0;uint64_t periodSum=0,padSum=0,overlapSum=0;std::vector<int> order;
    for(size_t j=0;j<runs.size();++j){const auto&run=runs[j];const auto&q=courses[run.colour];auto rank=courseRank(word,run.first);size_t cut=assignedOffset[rank];auto it=std::lower_bound(q.assigned.begin(),q.assigned.end(),cut);size_t before=it==q.assigned.begin()?q.assigned.back():*std::prev(it);int pad=11-int((cut+q.period.size()-before)%q.period.size());
        auto piece=cyclicText(q.period,cut,q.period.size()+pad);size_t actual=run.last-run.first+11;size_t matched=0;while(matched<std::min(actual,piece.size())&&word[run.first+matched]==piece[matched])++matched;
        bool exact=actual==piece.size()&&matched==actual;if(!exact)++failures;
        log<<"{\"position\":"<<j<<",\"course\":"<<q.root<<",\"period\":"<<q.period.size()<<",\"cut\":"<<cut<<",\"pad\":"<<pad<<",\"first\":"<<run.first<<",\"last\":"<<run.last<<",\"actual_piece_length\":"<<actual<<",\"expected_piece_length\":"<<piece.size()<<",\"matched_prefix\":"<<matched<<",\"exact\":"<<(exact?"true":"false")<<"}\n";
        periodSum+=q.period.size();padSum+=pad;if(!pieces.empty())overlapSum+=ov(pieces.back().substr(pieces.back().size()-11),piece.substr(0,11));pieces.push_back(std::move(piece));order.push_back(run.colour);}
    auto reconstructed=joinedWord(pieces);bool exact=reconstructed==word;std::ofstream report(out/"reconstruction-summary.json");report<<"{\"original_length\":"<<word.size()<<",\"required_courses\":"<<courses.size()<<",\"course_runs\":"<<runs.size()<<",\"courses_not_once\":"<<std::count_if(visits.begin(),visits.end(),[](int v){return v!=1;})<<",\"piece_span_mismatches\":"<<failures<<",\"period_sum\":"<<periodSum<<",\"pad_sum\":"<<padSum<<",\"overlap_sum\":"<<overlapSum<<",\"normalized_length\":"<<reconstructed.size()<<",\"byte_exact_reconstruction\":"<<(exact?"true":"false")<<"}\n";report.close();
    std::cout<<"courses="<<courses.size()<<" runs="<<runs.size()<<" piece_mismatches="<<failures<<" normalized_length="<<reconstructed.size()<<" exact="<<exact<<std::endl;
    if(reconstructed.size()<word.size()&&std::all_of(visits.begin(),visits.end(),[](int v){return v==1;})){std::ofstream candidate(out/("normalization-n11-"+std::to_string(reconstructed.size())+".txt"),std::ios::binary);candidate<<reconstructed;require(bool(candidate),"normalized candidate");}
    if(!exact||seconds==0){std::cout<<"exchange_not_run="<<(exact?"requested_audit_only":"basis_not_byte_exact")<<std::endl;return 0;}
    require(std::all_of(visits.begin(),visits.end(),[](int v){return v==1;}),"unique course inventory");std::ofstream trials(out/"exchanges.jsonl");auto start=std::chrono::steady_clock::now();int tested=0,gains=0;
    if(adjacent){adjacentSearch(courses,order,pieces,word,out,seconds,global);return 0;}
    // Expand the opening alphabet beyond constituent-cycle boundaries. A cut
    // inside a one-cost rotation orbit costs one or two extra wrapping symbols,
    // but may repay those symbols at its two literal outside attachments.
    // Every assigned window still fits in period + (n - backward gap).
    std::ofstream singles(out/"all-phase-single-cuts.jsonl");int64_t bestSingle=0;size_t bestPosition=0,bestCut=0;int bestPad=0;uint64_t allPhasePorts=0;
    for(size_t j=0;j<order.size();++j){const auto&q=courses[order[j]];auto left=j?frameBits(pieces[j-1],pieces[j-1].size()-11):0;auto right=j+1<pieces.size()?frameBits(pieces[j+1],0):0;
        int oldPad=int(pieces[j].size()-q.period.size());int oldPrice=oldPad-(j?frameOverlap(left,frameBits(pieces[j],0)):0)-(j+1<pieces.size()?frameOverlap(frameBits(pieces[j],pieces[j].size()-11),right):0);
        int bestPrice=30000,padAt=0;size_t cutAt=0;
        eachOpening(q,true,[&](uint64_t current,uint64_t previous,int pad,size_t cut){int price=pad-(j?frameOverlap(left,current):0)-(j+1<pieces.size()?frameOverlap(previous,right):0);if(price<bestPrice){bestPrice=price;cutAt=cut;padAt=pad;}++allPhasePorts;});
        int64_t saving=oldPrice-bestPrice;singles<<"{\"position\":"<<j<<",\"course\":"<<q.root<<",\"old_price\":"<<oldPrice<<",\"all_phase_minimum\":"<<bestPrice<<",\"saving\":"<<saving<<",\"winning_cut\":"<<cutAt<<",\"winning_pad\":"<<padAt<<"}\n";
        if(saving>bestSingle){bestSingle=saving;bestPosition=j;bestCut=cutAt;bestPad=padAt;}
    }
    std::cout<<"all_phase_ports="<<allPhasePorts<<" best_single_saving="<<bestSingle<<std::endl;
    if(bestSingle>0){auto changed=pieces;const auto&q=courses[order[bestPosition]];changed[bestPosition]=cyclicText(q.period,bestCut,q.period.size()+bestPad);auto candidate=joinedWord(changed);
        require(int64_t(word.size())-int64_t(candidate.size())==bestSingle,"all-phase literal saving identity");std::ofstream f(out/("single-phase-n11-"+std::to_string(candidate.size())+".txt"),std::ios::binary);f<<candidate;require(bool(f),"all-phase candidate");
        std::cout<<"all_phase_candidate="<<candidate.size()<<" position="<<bestPosition<<" pad="<<bestPad<<std::endl;}
    if(swaps){phaseBoundControls();for(bool allPhases:{false,true}){auto answer=phaseSwaps(courses,order,pieces,allPhases,out);if(answer.saving>0){auto changed=pieces;const auto&a=courses[order[answer.j]],&b=courses[order[answer.i]];changed[answer.i]=cyclicText(a.period,answer.atI.cut,a.period.size()+answer.atI.pad);changed[answer.j]=cyclicText(b.period,answer.atJ.cut,b.period.size()+answer.atJ.pad);auto candidate=joinedWord(changed);require(int64_t(word.size())-int64_t(candidate.size())==answer.saving,"literal two-site swap gain");std::ofstream f(out/((allPhases?"all-phase-":"constituent-phase-")+std::string("swap-n11-")+std::to_string(candidate.size())+".txt"),std::ios::binary);f<<candidate;require(bool(f),"swap candidate");}}
        return 0;}
    for(size_t j=0;j+width<=pieces.size();++j){double elapsed=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();if(elapsed>seconds)break;std::vector<int> rows;
        for(int k=0;k<width;++k){const auto&q=courses[order[j+k]];rows.insert(rows.end(),q.rows.begin(),q.rows.end());}
        std::string left=j?pieces[j-1].substr(pieces[j-1].size()-11):"",right=j+width<pieces.size()?pieces[j+width].substr(0,11):"";
        PhaseModel phase(m,rows,left,right);CoupledCourses cp({&phase});auto answer=solveCourses(cp,left,right,2ULL<<30);uint64_t old=0;for(int k=0;k<width;++k){old+=pieces[j+k].size();if(k)old-=ov(pieces[j+k-1].substr(pieces[j+k-1].size()-11),pieces[j+k].substr(0,11));}
        old-=ov(left,pieces[j].substr(0,11));old-=ov(pieces[j+width-1].substr(pieces[j+width-1].size()-11),right);int64_t gain=int64_t(old)-answer.cost;++tested;
        trials<<"{\"position\":"<<j<<",\"courses\":"<<width<<",\"ports\":"<<cp.V<<",\"original_local_length\":"<<old<<",\"optimal_local_length\":"<<answer.cost<<",\"saving\":"<<gain<<",\"solve_seconds\":"<<answer.seconds<<"}\n";trials.flush();
        if(gain>0){auto replacement=coupledWord(cp,answer);std::vector<std::string> changed;changed.insert(changed.end(),pieces.begin(),pieces.begin()+j);changed.push_back(std::move(replacement));changed.insert(changed.end(),pieces.begin()+j+width,pieces.end());auto candidate=joinedWord(changed);require(int64_t(word.size())-int64_t(candidate.size())==gain,"literal global saving identity");++gains;std::ofstream f(out/("exchange-n11-"+std::to_string(candidate.size())+".txt"),std::ios::binary);f<<candidate;require(bool(f),"exchange witness");std::cout<<"course_exchange_gain="<<gain<<" length="<<candidate.size()<<" position="<<j<<std::endl;break;}
        if(tested%100==0)std::cout<<"tested_course_windows="<<tested<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<std::endl;
    }
    std::ofstream final(out/"exchange-summary.json");final<<"{\"tested\":"<<tested<<",\"gains\":"<<gains<<",\"window_width\":"<<width<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count()<<",\"family\":\"all course orders, constituent-cycle start phases, fixed two outside frames\",\"independent_scan_required\":true}\n";
    return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 2;}
