int main1(int k,int m){
  int s, u, e, x;

  s=40;
  u=s;
  e=m;
  x=0;

  while (u>=1) {
      if (e+6<=s) {
          e = e+6;
      }
      else {
          e = s;
      }
      e = e+1;
  }

}
