int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=k;

  while (u<t) {
      v = v+2;
      v = v+u;
  }

}
