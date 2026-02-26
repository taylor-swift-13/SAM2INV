int main1(int m,int q){
  int t, l, v, f;

  t=m;
  l=t;
  v=-6;
  f=q;

  while (l>=1) {
      if (l<t/2) {
          v = v+f;
      }
      else {
          v = v+1;
      }
      v = v+3;
  }

}
