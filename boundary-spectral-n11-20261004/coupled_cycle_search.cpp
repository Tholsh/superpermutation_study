// Release module order AND module contiguity. In a selected neighboring bundle,
// every required cyclic course is occupied once, in any interleaved order and
// at any assigned constituent-cycle phase. This remains a restricted family:
// a course is not split into several visits. A literal word is the certificate.
#define PHASE_SPECTRAL_LIBRARY
#include "phase_cut_spectral.cpp"
#include <memory>

struct CycleBundle {std::vector<int> ids;std::string word;};
static std::vector<CycleBundle> loadBundles(const char* indexPath,const char* dataPath){
    std::ifstream index(indexPath),data(dataPath,std::ios::binary);std::string magic;
    int n;size_t count;require(bool(index>>magic>>n>>count)&&n==11&&bool(data),"bundle input");
    bool original=magic=="PIECES_NIBBLE_V1";
    require(original||magic=="CYCLE_BUNDLES_NIBBLE_V1","bundle format");
    std::vector<CycleBundle> result;uint64_t expected=0;
    for(size_t j=0;j<count;++j){CycleBundle b;size_t length;uint64_t offset;
        if(original){int id;require(bool(index>>id>>offset>>length),"piece index");b.ids.push_back(id);}
        else{size_t ni;require(bool(index>>ni)&&ni>0&&ni<=356,"bundle inventory count");
            b.ids.resize(ni);for(auto& id:b.ids)require(bool(index>>id),"bundle inventory");
            require(bool(index>>offset>>length),"bundle index");}
        require(offset==expected&&length>=11,"consecutive packed bundle offsets");b.word.resize(length);
        for(size_t k=0;k<length;k+=2){int x=data.get();require(x>=0,"packed input truncated");
            int a=x>>4,c=x&15;require(a<11,"packed symbol");b.word[k]=alphabet[a];
            if(k+1<length){require(c<11,"packed symbol");b.word[k+1]=alphabet[c];}
            else require(c==15,"unused nibble");}
        expected+=(length+1)/2;result.push_back(std::move(b));
    }
    require(!(index>>magic)&&data.get()==EOF,"trailing bundle data");return result;
}
static std::string bundleWord(const std::vector<CycleBundle>& bundles){
    std::string word;
    for(const auto&b:bundles){int k=word.empty()?0:ov(word.substr(word.size()-11),b.word.substr(0,11));word+=b.word.substr(k);}
    return word;
}
static uint64_t bundleLength(const std::vector<CycleBundle>& bundles){
    uint64_t result=0;const std::string* before=nullptr;
    for(const auto&b:bundles){result+=b.word.size()-(before?ov(before->substr(before->size()-11),b.word.substr(0,11)):0);before=&b.word;}
    return result;
}
static void saveBundles(const std::vector<CycleBundle>& bundles,const std::filesystem::path& out,const std::string& stem){
    std::ofstream index(out/(stem+"-index.txt")),data(out/(stem+".nibbles"),std::ios::binary);
    index<<"CYCLE_BUNDLES_NIBBLE_V1 11 "<<bundles.size()<<'\n';uint64_t offset=0;
    for(const auto&b:bundles){index<<b.ids.size();for(int id:b.ids)index<<' '<<id;
        index<<' '<<offset<<' '<<b.word.size()<<'\n';
        for(size_t k=0;k<b.word.size();k+=2){int a=int(alphabet.find(b.word[k]));
            int c=k+1<b.word.size()?int(alphabet.find(b.word[k+1])):15;data.put(char((a<<4)|c));}
        offset+=(b.word.size()+1)/2;}
    require(bool(index)&&bool(data),"bundle checkpoint output");
}
struct CoupledPort {const PhaseModel* model;int local,colour;};
struct CoupledColour {size_t start,count,base;};
struct CoupledCourses {
    int n=11,r=0,V=0,nkeys=0;int64_t bulk=0;
    std::vector<CoupledPort> ports;
    std::vector<CoupledColour> colours;
    std::vector<std::array<int,12>> pre,suf;
    CoupledCourses(const std::vector<const PhaseModel*>&models){
        uint64_t periods=0;
        for(const auto*p:models){int colourBase=r;r+=p->r;periods+=p->periodSum;
            for(int c=0;c<p->r;++c){size_t start=ports.size();
                for(int v=0;v<p->V;++v)if(p->c[v]==c)ports.push_back({p,v,colourBase+c});
                colours.push_back({start,ports.size()-start,0});}}
        V=int(ports.size());require(r>=2&&r<=14,"coupled colour bound");bulk=int64_t(periods)-n*(r-1);
        size_t base=0;
        for(auto&c:colours){c.base=base;base+=c.count*(size_t(1)<<(r-1));}
        require(base==size_t(V)*(size_t(1)<<(r-1)),"compressed occupation index cardinality");
        std::unordered_map<uint64_t,int>keys;keys.reserve(size_t(V)*14);pre.resize(V);suf.resize(V);
        auto key=[&](uint64_t x){return keys.emplace(x,int(keys.size())).first->second;};
        // Include the full 11-character seam. It can occur BETWEEN modules,
        // unlike the cross-colour seams inside one old module.
        for(int v=0;v<V;++v){const auto&q=ports[v];const auto&f=q.model->first[q.local];const auto&t=q.model->last[q.local];
            for(int k=0;k<=n;++k){pre[v][k]=key(code(f,0,k));suf[v][k]=key(code(t,n-k,k));}}
        nkeys=int(keys.size());
    }
    const std::string& first(int v)const{const auto&q=ports[v];return q.model->first[q.local];}
    const std::string& last(int v)const{const auto&q=ports[v];return q.model->last[q.local];}
    int pad(int v)const{const auto&q=ports[v];return q.model->port[q.local].pad;}
    static int compactMask(int mask,int c){return (mask&((1<<c)-1))|((mask>>(c+1))<<c);}
    size_t node(int mask,int v)const{int c=ports[v].colour;const auto&g=colours[c];
        return g.base+size_t(compactMask(mask,c))*g.count+(size_t(v)-g.start);}
};
struct CoupledAnswer {int64_t cost;std::vector<int> path;double seconds;uint64_t cells;};
static CoupledAnswer solveCourses(const CoupledCourses&p,const std::string&left,const std::string&right,uint64_t ramCap){
    auto started=std::chrono::steady_clock::now();const int inf=30000,full=(1<<p.r)-1;
    size_t cells=size_t(p.V)*(size_t(1)<<(p.r-1));
    require(cells<=ramCap/sizeof(int16_t),"coupled DP exceeds explicit RAM cap");
    std::vector<int16_t>d(cells,inf),bucket(p.nkeys,inf);
    for(int v=0;v<p.V;++v)d[p.node(1<<p.ports[v].colour,v)]=int16_t(p.pad(v)-ov(left,p.first(v)));
    for(int mask=1;mask<full;++mask){std::fill(bucket.begin(),bucket.end(),inf);
        for(int c=0;c<p.r;++c)if(mask&(1<<c)){const auto&g=p.colours[c];size_t begin=g.base+size_t(CoupledCourses::compactMask(mask,c))*g.count;
            for(size_t t=0;t<g.count;++t){int v=int(g.start+t),value=d[begin+t];if(value==inf)continue;
                for(int k=0;k<=p.n;++k){auto&b=bucket[p.suf[v][k]];b=std::min(int(b),value+p.n-k);}}}
        for(int c=0;c<p.r;++c)if(!(mask&(1<<c))){const auto&g=p.colours[c];size_t begin=g.base+size_t(CoupledCourses::compactMask(mask,c))*g.count;
            for(size_t t=0;t<g.count;++t){int v=int(g.start+t),best=inf;
                for(int k=0;k<=p.n;++k)best=std::min(best,int(bucket[p.pre[v][k]]));
                require(best<inf-30,"reachable occupation cell");d[begin+t]=int16_t(best+p.pad(v));}}
        if(mask%512==0)std::cout<<"coupled_mask="<<mask<<'/'<<full<<" colours="<<p.r<<" ports="<<p.V
            <<" seconds="<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<std::endl;
    }
    int best=inf,end=-1;
    for(int v=0;v<p.V;++v){int value=d[p.node(full,v)]-ov(p.last(v),right);if(value<best){best=value;end=v;}}
    require(end>=0,"coupled terminal reachable");CoupledAnswer a{p.bulk+best,{},0,cells};
    // Recover only one winning path, by checking the original literal seams.
    // No billion-cell parent array is required; all tied good paths stay valid.
    int mask=full,v=end;
    while(mask){a.path.push_back(v);int before=mask^(1<<p.ports[v].colour);
        if(!before){require(d[p.node(mask,v)]==p.pad(v)-ov(left,p.first(v)),"initial witness price");break;}
        int wanted=d[p.node(mask,v)],previous=-1;
        for(int c=0;c<p.r&&previous<0;++c)if(before&(1<<c)){const auto&g=p.colours[c];
            for(size_t t=0;t<g.count;++t){int u=int(g.start+t);
                if(d[p.node(before,u)]+p.n+p.pad(v)-ov(p.last(u),p.first(v))==wanted){previous=u;break;}}}
        require(previous>=0,"literal predecessor witness");mask=before;v=previous;
    }
    std::reverse(a.path.begin(),a.path.end());require(a.path.size()==size_t(p.r),"all selected courses occupied once");
    a.seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count();return a;
}
static std::string coupledWord(const CoupledCourses&p,const CoupledAnswer&a){
    std::string word;int used=0;
    for(int v:a.path){const auto&q=p.ports[v];require(!(used&(1<<q.colour)),"unique course witness");used|=1<<q.colour;
        auto piece=q.model->piece(q.local);int k=word.empty()?0:ov(word.substr(word.size()-11),piece.substr(0,11));word+=piece.substr(k);}
    require(used==(1<<p.r)-1,"complete course inventory");return word;
}
static std::string groupKey(const std::vector<int>&ids){std::ostringstream s;for(int id:ids)s<<id<<',';return s.str();}
struct CoupledJob {std::string leftKey,rightKey;int r;size_t rows;};
#ifndef COUPLED_CYCLE_LIBRARY
int main(int argc,char**argv)try{
    require(argc==10,"usage: coupled_cycle_search ROWS CIRCLES INDEX PACKED WORD FRESH_OUT MAX_COLOURS PASSES RAM_MIB");
    int maxColours=std::stoi(argv[7]),passes=std::stoi(argv[8]);uint64_t ramCap=std::stoull(argv[9])*(1ULL<<20);
    require(maxColours>=9&&maxColours<=14&&passes>=1&&passes<=10,"bounded coupled run");
    std::filesystem::path out(argv[6]);require(!std::filesystem::exists(out),"fresh coupled output");
    Model m;m.load(argv[1],argv[2]);auto bundles=loadBundles(argv[3],argv[4]);
    std::ifstream input(argv[5],std::ios::binary);require(bool(input),"input word");std::string original((std::istreambuf_iterator<char>(input)),{});
    while(!original.empty()&&(original.back()=='\n'||original.back()=='\r'))original.pop_back();
    require(bundleWord(bundles)==original,"exact initial literal reconstruction");
    std::map<int,int>colourCount;std::set<int>inventory;
    for(const auto&b:bundles)for(int id:b.ids){require(inventory.insert(id).second,"module inventory unique");
        std::set<int>c;for(int v:m.modules.at(id))c.insert(m.colour[v]);colourCount[id]=int(c.size());}
    std::map<int,std::unique_ptr<PhaseModel>>cache;
    auto context=[&](int id)->const PhaseModel*{auto&ptr=cache[id];if(!ptr){ptr=std::make_unique<PhaseModel>(m,m.modules.at(id),"","");
        std::cout<<"phase_context="<<id<<" colours="<<ptr->r<<" ports="<<ptr->V<<std::endl;}return ptr.get();};
    std::filesystem::create_directories(out);std::ofstream trials(out/"trials.jsonl"),gains(out/"gains.jsonl");
    auto started=std::chrono::steady_clock::now();int tested=0,changed=0,skipped=0;
    // Native control: the new compressed-index/full-seam recurrence agrees
    // with both pre-existing independent sparse and dense occupation DPs.
    int regular=-1;for(int id:inventory)if(m.modules.at(id).size()==72){regular=id;break;}
    require(regular>=0,"regular control inventory");const auto*control=context(regular);
    CoupledCourses singleton({control});auto controlAnswer=solveCourses(singleton,"0123456789A","A9876543210",ramCap);
    PhaseModel cp=*control;for(int v=0;v<cp.V;++v){cp.alpha[v]=11+cp.port[v].pad-ov("0123456789A",cp.first[v]);cp.beta[v]=11-ov(cp.last[v],"A9876543210");}
    int dense=phaseDenseMinimum(cp);require(dense==phaseMinimum(cp,false).objective&&controlAnswer.cost==singleton.bulk+dense-22,"three independent recurrence controls");
    auto controlText=coupledWord(singleton,controlAnswer);
    require(int64_t(controlText.size())-ov("0123456789A",controlText.substr(0,11))-ov(controlText.substr(controlText.size()-11),"A9876543210")==controlAnswer.cost,"control literal price");
    std::cout<<"compressed_dp_control=passed cost="<<controlAnswer.cost<<std::endl;
    for(int pass=1;pass<=passes;++pass){std::vector<CoupledJob>jobs;
        for(size_t j=0;j+1<bundles.size();++j){int r=0;size_t rows=0;bool irregular=false;
            for(size_t x=j;x<=j+1;++x)for(int id:bundles[x].ids){r+=colourCount.at(id);rows+=m.modules.at(id).size();irregular|=m.modules.at(id).size()!=72;}
            if(irregular&&r<=maxColours)jobs.push_back({groupKey(bundles[j].ids),groupKey(bundles[j+1].ids),r,rows});}
        std::sort(jobs.begin(),jobs.end(),[](const auto&a,const auto&b){return std::tie(a.r,a.rows,a.leftKey)<std::tie(b.r,b.rows,b.leftKey);});
        int passGains=0;
        for(const auto&job:jobs){size_t j=0;while(j+1<bundles.size()&&(groupKey(bundles[j].ids)!=job.leftKey||groupKey(bundles[j+1].ids)!=job.rightKey))++j;
            if(j+1>=bundles.size()){++skipped;continue;}
            std::vector<int>ids=bundles[j].ids;ids.insert(ids.end(),bundles[j+1].ids.begin(),bundles[j+1].ids.end());std::sort(ids.begin(),ids.end());
            std::vector<const PhaseModel*>models;for(int id:ids)models.push_back(context(id));
            std::cout<<"coupled_begin pass="<<pass<<" position="<<j<<" colours="<<job.r<<" inventory="<<groupKey(ids)<<std::endl;
            CoupledCourses p(models);require(p.r==job.r,"combined occupation count");
            std::string left=j?bundles[j-1].word.substr(bundles[j-1].word.size()-11):"";
            std::string right=j+2<bundles.size()?bundles[j+2].word.substr(0,11):"";
            auto oldPair=bundles[j].word;oldPair+=bundles[j+1].word.substr(ov(oldPair.substr(oldPair.size()-11),bundles[j+1].word.substr(0,11)));
            int64_t before=int64_t(oldPair.size())-ov(left,oldPair.substr(0,11))-ov(oldPair.substr(oldPair.size()-11),right);
            auto answer=solveCourses(p,left,right,ramCap);require(answer.cost<=before,"old interleaving remains a feasible course witness");
            ++tested;trials<<"{\"pass\":"<<pass<<",\"position\":"<<j<<",\"colours\":"<<p.r<<",\"ports\":"<<p.V<<",\"dp_bytes\":"<<answer.cells*2<<",\"old_cost\":"<<before<<",\"minimum_cost\":"<<answer.cost<<",\"saving\":"<<before-answer.cost<<",\"seconds\":"<<answer.seconds<<",\"module_order_and_interleaving_free\":true,\"inventory\":[";
            for(size_t k=0;k<ids.size();++k){if(k)trials<<',';trials<<ids[k];}trials<<"]}\n";trials.flush();
            if(answer.cost<before){auto word=coupledWord(p,answer);int64_t realized=int64_t(word.size())-ov(left,word.substr(0,11))-ov(word.substr(word.size()-11),right);
                require(realized==answer.cost,"coupled exact literal two-terminal price");uint64_t oldLength=bundleLength(bundles);
                bundles[j]={ids,std::move(word)};bundles.erase(bundles.begin()+j+1);uint64_t length=bundleLength(bundles);
                require(int64_t(oldLength)-int64_t(length)==before-answer.cost,"coupled whole-word gain identity");++changed;++passGains;
                auto whole=bundleWord(bundles);require(whole.size()==length,"coupled literal ledger");
                std::string stem="gain-"+std::to_string(changed)+"-n11-"+std::to_string(length);
                std::ofstream f(out/(stem+".txt"),std::ios::binary);f<<whole;require(bool(f),"literal improving word output");saveBundles(bundles,out,stem);
                gains<<"{\"pass\":"<<pass<<",\"position\":"<<j<<",\"saving\":"<<before-answer.cost<<",\"length\":"<<length<<",\"file\":\""<<stem<<".txt\",\"course_path\":[";
                for(size_t k=0;k<answer.path.size();++k){if(k)gains<<',';int v=answer.path[k];const auto&q=p.ports[v];
                    int moduleId=-1;for(size_t mi=0;mi<models.size();++mi)if(models[mi]==q.model)moduleId=ids[mi];
                    gains<<"{\"module\":"<<moduleId<<",\"colour\":"<<q.model->c[q.local]<<",\"port\":"<<q.local<<",\"cut\":"<<q.model->port[q.local].cut<<",\"pad\":"<<p.pad(v)<<"}";}
                gains<<"]}\n";gains.flush();}
            std::cout<<"coupled_done tested="<<tested<<" saving="<<before-answer.cost<<" length="<<bundleLength(bundles)<<" seconds="<<answer.seconds<<std::endl;
        }
        if(!passGains)break;
    }
    auto word=bundleWord(bundles);std::string stem="n11-"+std::to_string(word.size());
    std::ofstream f(out/(stem+".txt"),std::ios::binary);f<<word;require(bool(f),"final literal word output");saveBundles(bundles,out,"final-bundles");
    std::ofstream result(out/"result.json");result<<"{\"n\":11,\"baseline_length\":"<<original.size()<<",\"length\":"<<word.size()<<",\"pairs_solved\":"<<tested<<",\"changed_pairs\":"<<changed<<",\"stale_jobs_skipped\":"<<skipped<<",\"maximum_colours\":"<<maxColours<<",\"ram_cap_bytes\":"<<ramCap<<",\"seconds\":"<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<",\"module_interleaving_allowed\":true,\"whole_courses_once\":true,\"independent_scan_required\":true}\n";
    std::cout<<"coupled_final length="<<word.size()<<" changes="<<changed<<" tested="<<tested<<std::endl;return 0;
}catch(const std::exception&e){std::cerr<<e.what()<<'\n';return 1;}
#endif
