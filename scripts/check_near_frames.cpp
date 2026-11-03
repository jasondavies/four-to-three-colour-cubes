// Independent raw-geometry audit. This checks examples, not completeness of
// the all-n classification (which is proved symbolically in Lean).
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <queue>
#include <set>
#include <stdexcept>
#include <vector>
using Cube = std::array<int,6>;
using Counts = std::array<int,68>;
void require(bool b, const char* msg) { if (!b) throw std::runtime_error(msg); }
std::vector<Cube> rotations;
Cube rotate(const Cube& c, const Cube& r) {
  Cube v{}; for (int f=0; f<6; ++f) v[f]=c[r[f]]; return v;
}
Cube canonical(const Cube& c) {
  Cube best=c; for (const auto& r: rotations) best=std::min(best,rotate(c,r)); return best;
}
int cyclic(int a,int b,int c) { return std::min({16*a+4*b+c,16*b+4*c+a,16*c+4*a+b}); }
std::array<int,8> corners(const Cube& c) {
  std::array<int,8> v{};
  for (int p=0; p<8; ++p) {
    int x=p&1,y=(p>>1)&1,z=(p>>2)&1;
    v[p]=(x+y+z)%2 ? cyclic(c[x],c[4+z],c[2+y]) : cyclic(c[x],c[2+y],c[4+z]);
  }
  return v;
}
uint64_t corner_mask(const Cube& c) {
  uint64_t m=0; for (int k:corners(c)) m |= uint64_t(1)<<k; return m;
}
int edge_key(int a,int b) { return 4*std::min(a,b)+std::max(a,b); }
std::vector<std::array<int,2>> edge_faces;
uint32_t edge_mask(const Cube& c) {
  uint32_t m=0; for (auto e:edge_faces) m |= 1u<<edge_key(c[e[0]],c[e[1]]); return m;
}
struct Flow {
  struct Edge { int to,rev,cap; };
  std::vector<std::vector<Edge>> g; std::vector<int> level,next;
  explicit Flow(int n):g(n),level(n),next(n) {}
  void add(int a,int b,int cap) {
    g[a].push_back({b,int(g[b].size()),cap});
    g[b].push_back({a,int(g[a].size())-1,0});
  }
  int send(int a,int t,int cap) {
    if (a==t) return cap;
    for (int& j=next[a]; j<int(g[a].size()); ++j) {
      auto& e=g[a][j];
      if (e.cap && level[e.to]==level[a]+1) {
        int f=send(e.to,t,std::min(cap,e.cap));
        if (f) { e.cap-=f; g[e.to][e.rev].cap+=f; return f; }
      }
    }
    return 0;
  }
  int maxflow(int s,int t) {
    int ans=0;
    for (;;) {
      std::fill(level.begin(),level.end(),-1); level[s]=0;
      std::queue<int> q; q.push(s);
      while (!q.empty()) {
        int a=q.front(); q.pop();
        for (auto e:g[a]) if(e.cap && level[e.to]<0) {level[e.to]=level[a]+1;q.push(e.to);}
      }
      if (level[t]<0) return ans;
      std::fill(next.begin(),next.end(),0);
      while (int f=send(s,t,1000000)) ans+=f;
    }
  }
};
std::vector<Cube> sources,targets;
std::vector<uint64_t> cm;
std::vector<uint32_t> em;
bool builds(const Counts& x,const Cube& t,const std::array<int,3>& lengths) {
  // Six fixed exterior face colours; each edge direction is the omitted axis.
  Flow f(90); constexpr int sink=89; int demand=8;
  auto cc=corners(t);
  for(int i=0;i<68;++i) if(x[i]) f.add(0,1+i,x[i]);
  for(int p=0;p<20;++p) {
    int cap=1,key=0;
    if(p<8) key=cc[p];
    else {
      auto e=edge_faces[p-8]; int axis=3-e[0]/2-e[1]/2;
      cap=lengths[axis]-2; key=edge_key(t[e[0]],t[e[1]]); demand+=cap;
    }
    if(!cap) continue;
    f.add(69+p,sink,cap);
    for(int i=0;i<68;++i) if(x[i] && (p<8 ? bool(cm[i] & (uint64_t(1)<<key)) : bool(em[i] & (1u<<key))))
      f.add(1+i,69+p,cap);
  }
  return f.maxflow(0,sink)==demand;
}
int main() {
  Cube id{0,1,2,3,4,5}; std::set<Cube> rr{id}; std::vector<Cube> todo{id};
  for(size_t i=0;i<todo.size();++i) for(Cube g:{Cube{0,1,5,4,2,3},Cube{3,2,0,1,4,5}}) {
    Cube r=rotate(todo[i],g); if(rr.insert(r).second) todo.push_back(r);
  }
  rotations.assign(rr.begin(),rr.end()); require(rotations.size()==24,"rotation group");
  for(int a=0;a<6;++a) for(int b=a+1;b<6;++b) if(a/2!=b/2) edge_faces.push_back({a,b});
  std::set<Cube> ss,tt;
  for(int z=0;z<4096;++z) {
    int v=z; Cube c{}; std::set<int> colours;
    for(int& a:c) { a=v%4;v/=4;colours.insert(a); }
    if(colours.size()==4) ss.insert(canonical(c));
    if(colours.size()==3) tt.insert(canonical(c));
  }
  sources.assign(ss.begin(),ss.end());targets.assign(tt.begin(),tt.end());
  require(sources.size()==68 && targets.size()==120,"catalogue size");
  for(auto c:sources) {cm.push_back(corner_mask(c));em.push_back(edge_mask(c));}
  std::vector<int> ordinary,pairs,checkers; std::array<int,68> orientation{},bucket{};
  std::array<std::array<int,4>,2> triples{};
  uint64_t plus=0; for(auto k:std::array<std::array<int,3>,4>{{{0,1,2},{0,3,1},{0,2,3},{1,3,2}}}) plus |= uint64_t(1)<<cyclic(k[0],k[1],k[2]);
  for(int i=0;i<68;++i) {
    bool minimal=true;
    for(int j=0;j<68;++j) if(cm[j]!=cm[i] && (cm[j]&cm[i])==cm[j]) minimal=false;
    if(!minimal) continue;
    uint64_t tri=0;
    for(int k:corners(sources[i])) {
      int a=k/16,b=k/4%4,c=k%4;
      if(a!=b && a!=c && b!=c) tri |= uint64_t(1)<<k;
      for(int r=0;r<4;++r) if((a==r)+(b==r)+(c==r)>=2) bucket[i] |= 1<<r;
    }
    if(!bucket[i]) {checkers.push_back(i);continue;}
    ordinary.push_back(i); orientation[i]=(tri==plus ? 0:1);
    int mono=-1; for(int a=0;a<4;++a) if(cm[i] & (uint64_t(1)<<cyclic(a,a,a))) mono=a;
    if(mono>=0) triples[orientation[i]][mono]=i; else pairs.push_back(i);
  }
  require(ordinary.size()==32 && pairs.size()==24 && checkers.size()==6,"retained types");
  std::set<Cube> qrd,qdus;
  for(int a=0;a<4;++a) for(int b=0;b<4;++b) for(int c=0;c<4;++c) if(a!=b && a!=c && b!=c) {
    Cube q=canonical({b,c,a,a,a,a}),r=canonical({b,a,c,a,a,a}),d=canonical({a,a,b,b,c,c}),u=canonical({a,b,a,b,a,c});
    qrd.insert(q);qrd.insert(r);qrd.insert(d);qdus.insert(q);qdus.insert(d);qdus.insert(u);
  }
  require(qrd.size()==28 && qdus.size()==40,"restricted target counts");
  for(int n=2;n<=6;++n) {
    std::set<Counts> inventories;
    for(int i:ordinary) {
      Counts x{};
      for(int a=0;a<4;++a) x[triples[orientation[i]][a]]=4*n-1-((bucket[i]>>a)&1);
      bool pair=std::find(pairs.begin(),pairs.end(),i)!=pairs.end(); if(pair) x[i]++;
      require(std::accumulate(x.begin(),x.end(),0)==16*n-5,"near total");inventories.insert(x);
      for(auto t:targets) require(!builds(x,t,{n,n,n}),"near example solved");
      if(pair) for(int j=0;j<68;++j) {
        x[j]++;bool solved=false;
        for(auto t:(n==2?qrd:qdus)) if(builds(x,t,{n,n,n})) {solved=true;break;}
        require(solved,"pair case extension failed");x[j]--;
      }
    }
    require(inventories.size()==32,"distinct near cases");
    std::cout<<"n="<<n<<": 32 failures and 1632 pair-case extensions checked\n";
  }
  // The first new band: all weak compositions of deficit two, including
  // its n=3 stability boundary. Geometry and buckets were reconstructed above.
  for(int n : {3,4}) {
    std::set<Counts> failures;
    int maximal=0, extensions=0;
    for(int side=0;side<2;++side) {
      std::vector<int> pp;
      for(int i:pairs) if(orientation[i]==side) pp.push_back(i);
      require(pp.size()==12,"stability pair coordinates");
      for(int u=0;u<16;++u) for(int v=u;v<16;++v) {
        Counts x{};
        for(int a=0;a<4;++a) x[triples[side][a]]=4*n-1;
        for(int coordinate : {u,v}) {
          if(coordinate<12) {
            int i=pp[coordinate]; x[i]++;
            for(int a=0;a<4;++a) if(bucket[i]&(1<<a)) x[triples[side][a]]--;
          } else x[triples[side][coordinate-12]]--;
        }
        require(std::accumulate(x.begin(),x.end(),0)==16*n-6,"stability total");
        require(failures.insert(x).second,"stability parametrisation collision");
        for(auto t:targets) require(!builds(x,t,{n,n,n}),"stable example solved");
        if(v<12) {
          maximal++;
          for(int j=0;j<68;++j) {
            x[j]++; bool solved=false;
            for(auto t:qdus) if(builds(x,t,{n,n,n})) {solved=true;break;}
            require(solved,"saturated stability extension failed"); x[j]--; extensions++;
          }
        } else {
          x[triples[side][v-12]]++;
          for(auto t:targets) require(!builds(x,t,{n,n,n}),"positive slack failed to extend");
        }
      }
    }
    require(failures.size()==272 && maximal==156,"stability binomial counts");
    std::cout<<"n="<<n<<": 272 deficit-two failures, 156 maximal, "<<extensions
             <<" maximal extensions and 116 slack extensions checked\n";
  }
  for(int k=1;k<=4;++k) {
    Counts x{}; for(int i:checkers) x[i]=2*k;
    for(auto t:targets) for(auto r:rotations) require(!builds(x,rotate(t,r),{2,2,3*k}),"thin checkerboard box solved");
  }
  std::cout<<"28/40 target counts and thin-box controls k=1..4 checked.\n";
}
