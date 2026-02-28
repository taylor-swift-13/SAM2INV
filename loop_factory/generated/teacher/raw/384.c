int main1(int m,int q){
  int h, s, v, k;

  h=q;
  s=0;
  v=h;
  k=0;

  while (s<h) {
      v = v*2+4;
      k = k*v+4;
      s = s+1;
  }

}
