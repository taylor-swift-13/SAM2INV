int main1(int k,int p){
  int u, a, o, v;

  u=(k%17)+14;
  a=1;
  o=0;
  v=-5;

  while (o<u) {
      if (o>=u/2) {
          v = v+2;
      }
      o = o+1;
  }

}
