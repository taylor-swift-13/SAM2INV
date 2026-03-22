int main1(){
  int m, tj, k, f6hh, t, sea;

  m=39;
  tj=(1%28)+8;
  k=(1%22)+5;
  f6hh=0;
  t=13;
  sea=m;

  while (1) {
      if (!(k!=0)) {
          break;
      }
      if (k%2==1) {
          f6hh += tj;
          k = k - 1;
      }
      tj = 2*tj;
      k = k/2;
      t = t*4;
      sea = sea*4+(k%6)+2;
  }

}
