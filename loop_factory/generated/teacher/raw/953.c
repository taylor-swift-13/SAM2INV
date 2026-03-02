int main1(int a,int m){
  int t, k, o;

  t=a;
  k=0;
  o=t;

  while (k<=t-1) {
      o = o+k;
      if (o+6<t) {
          o = o+1;
      }
      k = k+1;
  }

}
