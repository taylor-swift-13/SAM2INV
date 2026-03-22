int main1(int g){
  int mbtb, a, bw, q0, fc;

  mbtb=g+13;
  a=1;
  bw=a;
  q0=0;
  fc=g;

  while (a<mbtb) {
      q0 = q0/4;
      bw = bw*4;
      fc += 2;
      a = mbtb;
  }

}
