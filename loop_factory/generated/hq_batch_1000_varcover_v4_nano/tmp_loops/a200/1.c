int main1(int b,int k,int m,int n){
  int l, i, v, u, d, r;

  l=(k%8)+4;
  i=l;
  v=i;
  u=i;
  d=i;
  r=0;

  while (i>0) {
      if (i%4==0) {
          v = v+1;
      }
      else {
          u = u+1;
      }
      if (i%4==1) {
          d = d+1;
      }
      else {
      }
      v = v*2+2;
      u = u*v+2;
      u = u*u+r;
      if ((i%2)==0) {
          u = u*2;
      }
      d = r*r;
      v = v*v+r;
  }

}
