int main1(int i){
  int iz, bw, ujx, bk, u, nj, s9q, v0;

  iz=i;
  bw=0;
  ujx=90;
  bk=0;
  u=1;
  nj=0;
  s9q=bw;
  v0=iz;

  while (ujx>0&&bw<iz) {
      if (ujx<u) {
          nj = ujx;
      }
      else {
          nj = u;
      }
      bk += nj;
      ujx -= nj;
      if (bw%2==0) {
          u += 2;
      }
      else {
          u = u + 1;
      }
      s9q += 2;
      bw++;
      v0 = v0 + bw;
      i = i + u;
  }

}
