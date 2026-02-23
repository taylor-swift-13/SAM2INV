int main1(int k,int m){
  int t, u, v;

  t=(m%14)+15;
  u=0;
  v=2;

  while (u<t) {
      v = v+1;
      v = v+v;
      u = u+1;
  }

}
