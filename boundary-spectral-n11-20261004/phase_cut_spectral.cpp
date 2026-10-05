// Expanded n=11 boundary family: every row's assigned-cycle starting phase is
// an allowed cut, not only the row head. Exact occupation is kept by a minimal
// wrapping prefix. Whole required cycles are still visited once; modules and
// their global order remain fixed. No claim of a global optimum.
#define BOUNDARY_SPECTRAL_LIBRARY
#include "boundary_spectral.cpp"

static std::string cyclicText(const std::string&s,size_t begin,size_t length) {
    require(!s.empty(),"nonempty period");std::string out;out.reserve(length);begin%=s.size();
    while(length){size_t take=std::min(length,s.size()-begin);out.append(s,begin,take);length-=take;begin=0;}
    return out;
}
static bool permutationFrame(const std::string&s){auto x=s;std::sort(x.begin(),x.end());return x==alphabet.substr(0,11);}
struct PhasePort {int colour;size_t cut;int pad;};
struct PhaseModel {
    int n=11,h=11,r=0,V=0,nkeys=0,maxStep=20;
    uint64_t periodSum=0;
    std::vector<std::string>periods,first,last;
    std::vector<PhasePort>port;
    std::vector<int>alpha,beta,c,colourSize;
    std::vector<std::array<int,11>>pre,suf;
    PhaseModel(const Model&m,const std::vector<int>&vs,const std::string&left,const std::string&right){
        std::map<int,int>root;for(int v:vs)root.emplace(m.colour[v],v);
        for(auto[rootId,start]:root){(void)rootId;int colour=r++;std::string text=m.head[start];
            std::vector<size_t>cuts,assigned;std::vector<int>pads;uint64_t offset=0;int at=start;
            do{const auto&w=m.payload[at];int visible=int((w.size()-(m.n-2))/(m.n+1));
                require(w.size()==size_t((m.n+1)*visible+m.n-2),"visible length identity");
                for(int j=0;j<visible;++j){cuts.push_back(offset+size_t(j)*(m.n+1));pads.push_back(j?m.n-2:m.h);
                    for(int i=0;i<m.n;++i)assigned.push_back(offset+size_t(j)*(m.n+1)+i);}
                text+=w.substr(m.h);offset+=w.size()-m.h;at=m.next[at];
            }while(at!=start);
            require(text.size()==offset+m.h&&text.compare(offset,m.h,text,0,m.h)==0,"cyclic literal closure");
            text.resize(offset);require(std::is_sorted(assigned.begin(),assigned.end())&&
                std::adjacent_find(assigned.begin(),assigned.end())==assigned.end()&&assigned.back()<offset,"assigned starts partition");
            periodSum+=offset;periods.push_back(std::move(text));colourSize.push_back(int(cuts.size()));
            for(size_t j=0;j<cuts.size();++j){size_t cut=cuts[j];auto it=std::lower_bound(assigned.begin(),assigned.end(),cut);
                size_t before=it==assigned.begin()?assigned.back():*std::prev(it);
                size_t backward=(cut+offset-before)%offset;require(backward>0&&backward<=size_t(m.n),"preceding assigned window");
                int pad=m.n-int(backward);require(pad==pads[j],"minimum occupation-preserving wrapping prefix");
                port.push_back({colour,cut,pad});c.push_back(colour);
                first.push_back(cyclicText(periods.back(),cut,m.n));
                last.push_back(cyclicText(periods.back(),(cut+offset+pad-m.n)%offset,m.n));
                require(permutationFrame(first.back())&&permutationFrame(last.back()),"literal phase boundary permutations");
                alpha.push_back(m.n+pad-ov(left,first.back()));beta.push_back(m.n-ov(last.back(),right));}
        }
        V=int(port.size());require(r>=2&&r<=8,"n=11 selected module size");
        std::unordered_map<uint64_t,int>keys;keys.reserve(size_t(V)*18);
        auto key=[&](uint64_t x){return keys.emplace(x,int(keys.size())).first->second;};pre.resize(V);suf.resize(V);
        std::unordered_map<uint64_t,int>firstColour;firstColour.reserve(V*2);
        for(int v=0;v<V;++v){require(firstColour.emplace(code(first[v],0,n),c[v]).second,"distinct assigned entry permutations");
            for(int k=0;k<n;++k){pre[v][k]=key(code(first[v],0,k));suf[v][k]=key(code(last[v],n-k,k));}}
        for(int v=0;v<V;++v){auto it=firstColour.find(code(last[v],0,n));
            require(it==firstColour.end()||it->second==c[v],"full-frame overlap cannot cross occupation colours");}
        nkeys=int(keys.size());
    }
    int distance(int u,int v)const{return n+port[v].pad-ov(last[u],first[v]);}
    std::string piece(int v)const{const auto&p=port[v];return cyclicText(periods[p.colour],p.cut,periods[p.colour].size()+p.pad);}
};
struct PhaseAnswer {int objective=0;std::vector<int>path;};
static PhaseAnswer phaseMinimum(const PhaseModel&p,bool witness=true){
    int full=(1<<p.r)-1,inf=30000;size_t cells=size_t(full+1)*p.V;
    require(cells<UINT32_MAX,"predecessor index");std::vector<int16_t>d(cells,inf);
    std::vector<uint32_t>parent(witness?cells:0,UINT32_MAX),owner(p.nkeys);
    std::vector<int>bucket(p.nkeys,inf);
    for(int v=0;v<p.V;++v)d[size_t(1<<p.c[v])*p.V+v]=p.alpha[v];
    for(int mask=1;mask<full;++mask){std::fill(bucket.begin(),bucket.end(),inf);
        for(int u=0;u<p.V;++u)if(mask&(1<<p.c[u])){uint32_t index=uint32_t(size_t(mask)*p.V+u);int value=d[index];
            if(value==inf)continue;
            for(int k=0;k<p.n;++k){int key=p.suf[u][k],candidate=value+p.n-k;
                if(candidate<bucket[key]){bucket[key]=candidate;owner[key]=index;}}}
        for(int v=0;v<p.V;++v)if(!(mask&(1<<p.c[v]))){int best=inf;uint32_t before=UINT32_MAX;
            for(int k=0;k<p.n;++k){int key=p.pre[v][k];if(bucket[key]<best){best=bucket[key];before=owner[key];}}
            size_t index=size_t(mask|(1<<p.c[v]))*p.V+v;d[index]=int16_t(best+p.port[v].pad);
            if(witness)parent[index]=before;}}
    PhaseAnswer answer;answer.objective=inf;uint32_t at=UINT32_MAX;
    for(int v=0;v<p.V;++v){uint32_t index=uint32_t(size_t(full)*p.V+v);int a=d[index]+p.beta[v];
        if(a<answer.objective){answer.objective=a;at=index;}}
    if(witness){for(;at!=UINT32_MAX;at=parent[at])answer.path.push_back(at%p.V);
        std::reverse(answer.path.begin(),answer.path.end());require(answer.path.size()==size_t(p.r),"complete colour path");}
    return answer;
}
static int phaseDenseMinimum(const PhaseModel&p){
    require(p.V<=1000,"dense control guard");int full=(1<<p.r)-1,inf=30000;
    std::vector<uint8_t>cost(size_t(p.V)*p.V);for(int u=0;u<p.V;++u)for(int v=0;v<p.V;++v)cost[size_t(u)*p.V+v]=p.distance(u,v);
    std::vector<int16_t>d(size_t(full+1)*p.V,inf);
    for(int v=0;v<p.V;++v)d[size_t(1<<p.c[v])*p.V+v]=p.alpha[v];
    for(int mask=1;mask<full;++mask)for(int u=0;u<p.V;++u)if(mask&(1<<p.c[u])){
        int value=d[size_t(mask)*p.V+u];if(value==inf)continue;
        for(int v=0;v<p.V;++v)if(!(mask&(1<<p.c[v]))){auto&to=d[size_t(mask|(1<<p.c[v]))*p.V+v];to=std::min(int(to),value+cost[size_t(u)*p.V+v]);}}
    int best=inf;for(int v=0;v<p.V;++v)best=std::min(best,int(d[size_t(full)*p.V+v])+p.beta[v]);return best;
}
static std::vector<I128>phasePolynomial(const PhaseModel&p){
    int full=(1<<p.r)-1,D=p.maxStep*p.r+p.n,W=D+1;
    size_t cells=size_t(full+1)*p.V*W;require(cells<=2500000000ULL/sizeof(I128),"exact phase polynomial RAM guard");
    std::vector<I128>d(cells),bucket(size_t(p.nkeys)*W);
    for(int v=0;v<p.V;++v)d[(size_t(1<<p.c[v])*p.V+v)*W+p.alpha[v]]=1;
    for(int mask=1;mask<full;++mask){int top=p.maxStep*__builtin_popcount(unsigned(mask));std::fill(bucket.begin(),bucket.end(),0);
        for(int u=0;u<p.V;++u)if(mask&(1<<p.c[u])){const I128*from=&d[(size_t(mask)*p.V+u)*W];
            for(int k=0;k<p.n;++k){I128*to=&bucket[size_t(p.suf[u][k])*W];
                for(int j=0;j<=top;++j)if(from[j])to[j]=addChecked(to[j],from[j]);}}
        const I128*base=&bucket[size_t(p.pre[0][0])*W];
        for(int v=0;v<p.V;++v)if(!(mask&(1<<p.c[v]))){I128*to=&d[(size_t(mask|(1<<p.c[v]))*p.V+v)*W];
            for(int j=0;j<=top;++j){I128 remaining=base[j];int pad=p.port[v].pad;
                for(int k=1;k<p.n;++k){I128 count=bucket[size_t(p.pre[v][k])*W+j];require(remaining>=count,"phase overlap exclusion");remaining-=count;
                    if(count)to[j+p.n+pad-k]=addChecked(to[j+p.n+pad-k],count);}
                if(remaining)to[j+p.n+pad]=addChecked(to[j+p.n+pad],remaining);}}
    }
    std::vector<I128>P(W);for(int v=0;v<p.V;++v)for(int j=0;j<=D-p.beta[v];++j)
        P[j+p.beta[v]]=addChecked(P[j+p.beta[v]],d[(size_t(full)*p.V+v)*W+j]);
    I128 total=0,expected=1;for(int s:p.colourSize){require(U128(expected)<=maxSigned/U128(s),"phase path count bound");expected*=s;}
    for(int j=2;j<=p.r;++j){require(U128(expected)<=maxSigned/U128(j),"phase order count bound");expected*=j;}
    for(I128 x:P)total=addChecked(total,x);
    require(total==expected,"phase exact total path count");return P;
}
static void phaseApply(const PhaseModel&p,long double z,const std::vector<long double>&x,std::vector<long double>&y){
    int full=(1<<p.r)-1;std::fill(y.begin(),y.end(),0);y[0]=x[1];std::vector<long double>powers(2*p.n+1,1);
    for(size_t j=1;j<powers.size();++j)powers[j]=powers[j-1]*z;
    for(int v=0;v<p.V;++v)y[2+size_t(1<<p.c[v])*p.V+v]=x[0]*powers[p.alpha[v]];
    std::vector<long double>bucket(p.nkeys);
    for(int mask=1;mask<full;++mask){std::fill(bucket.begin(),bucket.end(),0);
        for(int u=0;u<p.V;++u)if(mask&(1<<p.c[u]))for(int k=0;k<p.n;++k)bucket[p.suf[u][k]]+=x[2+size_t(mask)*p.V+u];
        long double base=bucket[p.pre[0][0]];
        for(int v=0;v<p.V;++v)if(!(mask&(1<<p.c[v]))){long double remaining=base,value=0;int pad=p.port[v].pad;
            for(int k=1;k<p.n;++k){long double a=bucket[p.pre[v][k]];remaining-=a;value+=a*powers[p.n+pad-k];}
            value+=remaining*powers[p.n+pad];y[2+size_t(mask|(1<<p.c[v]))*p.V+v]=value;}}
    for(int v=0;v<p.V;++v)y[1]+=x[2+size_t(full)*p.V+v]*powers[p.beta[v]];
}
static Numeric phaseNumerical(const PhaseModel&p,const std::vector<I128>&P,long double z){
    Numeric a;a.rho=std::pow(evaluate(P,z),1.L/(p.r+2));size_t N=2+(size_t(1)<<p.r)*p.V;
    std::vector<long double>x(N),y(N);x[0]=1;
    for(int j=0;j<p.r+2;++j){phaseApply(p,z,x,y);x.swap(y);}long double value=evaluate(P,z);
    a.krylovError=std::abs(x[0]-value)/value;for(size_t j=1;j<N;++j)require(std::abs(x[j])<1e-15L*value,"phase Krylov support");
    x.assign(N,0);x[0]=1;
    for(int iter=1;iter<=1600;++iter){phaseApply(p,z,x,y);long double norm=0;
        for(size_t j=0;j<N;++j){y[j]=x[j]+y[j]/a.rho;norm+=std::abs(y[j]);}
        long double delta=0;for(size_t j=0;j<N;++j){y[j]/=norm;delta+=std::abs(y[j]-x[j]);}x.swap(y);
        a.iterations=iter;if(delta<1e-14L)break;}
    phaseApply(p,z,x,y);long double sx=0,sy=0;for(size_t j=0;j<N;++j){sx+=x[j];sy+=y[j];}
    a.measured=sy/sx;long double err=0;for(size_t j=0;j<N;++j)err+=std::abs(y[j]-a.rho*x[j]);a.residual=err/(a.rho*sx);
    require(a.residual<1e-10L&&a.krylovError<1e-10L,"phase numerical spectral agreement");return a;
}
static std::string phaseReplacement(const PhaseModel&p,const PhaseAnswer&a){
    std::string piece;std::set<int>colours;
    for(int v:a.path){require(colours.insert(p.c[v]).second,"phase colour used once");auto word=p.piece(v);
        require(word.substr(0,p.n)==p.first[v]&&word.substr(word.size()-p.n)==p.last[v],"expanded literal port frames");
        int overlap=piece.empty()?0:ov(piece.substr(piece.size()-p.n),p.first[v]);piece+=word.substr(overlap);}
    require(colours.size()==size_t(p.r),"expanded occupation complete");return piece;
}
static uint64_t joinedLength(const std::vector<std::string>&pieces){uint64_t L=0;
    for(size_t j=0;j<pieces.size();++j)L+=pieces[j].size()-(j?ov(pieces[j-1].substr(pieces[j-1].size()-11),pieces[j].substr(0,11)):0);
    return L;
}
static std::string joinedWord(const std::vector<std::string>&pieces){std::string word;word.reserve(joinedLength(pieces));
    for(const auto&piece:pieces){int k=word.empty()?0:ov(word.substr(word.size()-11),piece.substr(0,11));word+=piece.substr(k);}return word;
}
#ifndef PHASE_SPECTRAL_LIBRARY
int main(int argc,char**argv)try{
    require(argc==6,"usage: phase_cut_spectral ROWS CIRCLES WHOLE_ROW_WORD FRESH_OUT MAX_PASSES");
    std::filesystem::path out(argv[4]);require(!std::filesystem::exists(out),"fresh phase output");std::filesystem::create_directories(out);
    Model m;m.load(argv[1],argv[2]);Scan original=scan(m,argv[3]);require(!original.missing&&!original.multiple&&!original.interleaved,"whole-row initial control");
    std::vector<std::string>pieces;for(int id:original.order){auto[a,b]=original.intervals.at(id);pieces.push_back(original.word.substr(a,b-a));}
    require(joinedWord(pieces)==original.word,"exact baseline module/frame reconstruction");
    std::ofstream log(out/"coordinate.jsonl"),metrics(out/"phase-ports.jsonl");int changes=0,passes=0;uint64_t allPorts=0;double spectralSeconds=0;
    auto started=std::chrono::steady_clock::now();int maxPasses=std::stoi(argv[5]);require(maxPasses>=1&&maxPasses<=10,"bounded passes");
    for(int pass=1;pass<=maxPasses;++pass){int gains=0;for(size_t j=0;j<pieces.size();++j){int id=original.order[j];
        std::string left=j?pieces[j-1].substr(pieces[j-1].size()-11):"";
        std::string right=j+1<pieces.size()?pieces[j+1].substr(0,11):"";
        PhaseModel p(m,m.modules.at(id),left,right);auto answer=phaseMinimum(p);
        int64_t constant=int64_t(p.periodSum)-p.n*(p.r+1),candidate=constant+answer.objective;
        int64_t before=int64_t(pieces[j].size())-ov(left,pieces[j].substr(0,11))-ov(pieces[j].substr(pieces[j].size()-11),right);
        if(pass==1){allPorts+=p.V;metrics<<"{\"position\":"<<j<<",\"module\":"<<id<<",\"colours\":"<<p.r<<",\"phase_ports\":"<<p.V<<",\"occupation_dimension\":"<<(2+uint64_t(p.V)*(uint64_t(1)<<(p.r-1)))<<",\"scalar_spectral_block\":"<<p.r+2<<",\"minimum_adjusted_exponent\":"<<answer.objective<<",\"current_two_terminal_cost\":"<<before<<",\"optimal_two_terminal_cost\":"<<candidate<<"}\n";metrics.flush();}
        if(pass==1&&j==0){require(answer.objective==phaseDenseMinimum(p),"phase dense min-plus control");
            auto timer=std::chrono::steady_clock::now();auto P=phasePolynomial(p);int lo=0,hi=int(P.size())-1;while(!P[lo])++lo;while(!P[hi])--hi;
            require(lo==answer.objective,"phase coefficient extraction agrees with exact shortest path");
            std::ofstream f(out/"phase-polynomial.json");f<<"{\"module\":"<<id<<",\"constant\":"<<constant<<",\"minimum_exponent\":"<<lo<<",\"degree\":"<<hi<<",\"coefficients\":[";
            for(size_t k=0;k<P.size();++k){if(k)f<<',';f<<'"'<<decimal(U128(P[k]))<<'"';}f<<"]}\n";
            std::ofstream ns(out/"phase-spectrum.json");auto num=phaseNumerical(p,P,0.8L);ns<<std::setprecision(20)<<"{\"z\":0.8,\"analytic_perron_root\":"<<num.rho<<",\"unreduced_numeric_perron_root\":"<<num.measured<<",\"relative_residual\":"<<num.residual<<",\"krylov_relative_error\":"<<num.krylovError<<",\"iterations\":"<<num.iterations<<"}\n";
            spectralSeconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-timer).count();}
        if(candidate<before){auto replacement=phaseReplacement(p,answer);int64_t realized=int64_t(replacement.size())-ov(left,replacement.substr(0,11))-ov(replacement.substr(replacement.size()-11),right);
            require(realized==candidate,"phase exact literal objective");uint64_t oldLength=joinedLength(pieces);pieces[j]=std::move(replacement);
            uint64_t newLength=joinedLength(pieces);require(int64_t(newLength)-int64_t(oldLength)==candidate-before,"two-terminal global length identity");
            ++gains;++changes;log<<"{\"pass\":"<<pass<<",\"position\":"<<j<<",\"module\":"<<id<<",\"saving\":"<<before-candidate<<",\"length\":"<<newLength<<"}\n";log.flush();}
        if(j%25==0)std::cout<<"phase_pass="<<pass<<" modules="<<j+1<<" length="<<joinedLength(pieces)<<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<std::endl;
    }passes=pass;if(!gains)break;}
    auto word=joinedWord(pieces);require(word.size()==joinedLength(pieces),"final word ledger");std::string filename="n11-"+std::to_string(word.size())+".txt";
    std::ofstream output(out/filename,std::ios::binary);output<<word;require(bool(output),"phase output word");
    // Preserve the actual new pieces, including the altered open connector.
    // Two four-bit symbols per byte; a final unused nibble is 15. The index
    // retains exact lengths so the literal cut audit needs no old row parsing.
    std::ofstream packed(out/"pieces.nibbles",std::ios::binary),index(out/"pieces-index.txt");
    index<<"PIECES_NIBBLE_V1 11 "<<pieces.size()<<'\n';uint64_t byteOffset=0;
    for(size_t j=0;j<pieces.size();++j){const auto&s=pieces[j];index<<original.order[j]<<' '<<byteOffset<<' '<<s.size()<<'\n';
        for(size_t k=0;k<s.size();k+=2){int a=int(alphabet.find(s[k])),b=k+1<s.size()?int(alphabet.find(s[k+1])):15;
            packed.put(char((a<<4)|b));}byteOffset+=(s.size()+1)/2;}
    require(bool(packed)&&bool(index),"packed literal pieces");
    std::ofstream result(out/"result.json");result<<"{\"n\":11,\"baseline_length\":"<<original.length<<",\"length\":"<<word.size()<<",\"modules\":"<<pieces.size()<<",\"phase_ports\":"<<allPorts<<",\"coordinate_passes\":"<<passes<<",\"accepted_changes\":"<<changes<<",\"spectral_seconds\":"<<spectralSeconds<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<",\"fixed_module_order\":true,\"whole_cycles_once\":true,\"independent_scan_required\":true}\n";
    std::cout<<"phase_final_length="<<word.size()<<" changes="<<changes<<std::endl;return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
#endif
