int main1(int p,int q){
  int y, d, k, v;

  y=p;
  d=0;
  k=q;
  v=p;

  while (d<y) {
      k = k+3;
      v = v+2;
      if ((d%7)==0) {
          k = k-(-3);
      }
      d = d+1;
  }

}
