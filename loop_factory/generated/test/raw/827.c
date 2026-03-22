int main1(int b){
  int k, c1eo, q6nv, y, s2tw, hj;

  k=b;
  c1eo=0;
  q6nv=1;
  y=c1eo;
  s2tw=6;
  hj=(b%6)+2;

  while (s2tw<=k-1) {
      q6nv = q6nv*hj+4;
      y = y*hj;
      b = b + q6nv;
      s2tw = k;
  }

}
