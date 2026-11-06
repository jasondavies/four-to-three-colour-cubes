// Enumerate all six checkerboard weights of total at most N.
// Check the triangle conclusion for EVERY nonempty good set that contains
// all vertices of incident weight >=8. No source/target catalogue is used.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
using A = std::array<int, 6>;
constexpr int ends[6][2]={{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
std::uint64_t run(int a,int b,int c) {
  int N=std::max({16*a-3,4*(a+b+c)-16,(24*c-1)/5});
  std::uint64_t checked=0;
  A x{};
  auto visit=[&]() {
    int deg[4]={},valid=0,forced=0;
    for(int e=0;e<6;e++)for(int k=0;k<2;k++)deg[ends[e][k]]+=x[e];
    for(int v=0;v<4;v++) {
      if(deg[v]>=8)forced|=1<<v;
      std::array<int,3> t{};int n=0;
      for(int e=0;e<6;e++)if(ends[e][0]!=v && ends[e][1]!=v)t[n++]=x[e];
      std::sort(t.begin(),t.end());
      if(t[0]<=N-4*c && t[1]<=N-4*b && t[2]<=N-4*a)valid|=1<<v;
    }
    // Every allowed good set contains one of these four minimal seeds.
    for(int v=0;v<4;v++)if(!((forced|(1<<v))&valid))
      throw std::runtime_error("weighted triangle counterexample");
    checked++;
  };
  auto rec=[&](auto&& self,int i,int remaining)->void {
    if(i==6){visit();return;}
    for(x[i]=0;x[i]<=remaining;x[i]++)self(self,i+1,remaining-x[i]);
  };
  rec(rec,0,N);
  std::cout<<a<<'x'<<b<<'x'<<c<<" N="<<N<<" weight vectors="<<checked<<" passed\n";
  return checked;
}
int main() {
  std::uint64_t total=0;
  for(auto shape:std::array<std::array<int,3>,5>{{{2,4,5},{2,4,6},{2,5,5},{3,3,9},{3,3,10}}})
    total+=run(shape[0],shape[1],shape[2]);
  std::cout<<"Total: "<<total<<" weighted configurations; all allowed good sets checked.\n";
}
