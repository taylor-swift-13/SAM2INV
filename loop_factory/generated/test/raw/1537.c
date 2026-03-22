int main1(){
  int g0, bj, b, l, q, h8bz, k, ox, z, c;

  g0=1;
  bj=0;
  b=bj;
  l=bj;
  q=bj;
  h8bz=bj;
  k=2;
  ox=g0;
  z=g0;
  c=bj;

  while (bj < g0) {
      bj = bj + 1;
      if ((bj % 2) == 0) {
          b += 1;
      }
      if ((bj % 3) == 0) {
          z += 1;
      }
      if ((bj % 5) == 0) {
          c = c + 1;
      }
      k = k + c;
      h8bz += b;
      ox = (ox+b)%7;
      l += z;
      q += h8bz;
      h8bz += l;
  }

}
