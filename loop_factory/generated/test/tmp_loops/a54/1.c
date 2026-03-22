int main1(int m){
  int ecb, m9hv, jp, nrw, e6i4, h5v, d5;

  ecb=m+19;
  m9hv=0;
  jp=m;
  nrw=0;
  e6i4=ecb;
  h5v=7;
  d5=ecb;

  while (1) {
      if (!(m9hv<=ecb-1)) {
          break;
      }
      m9hv++;
      if (e6i4<=nrw) {
          nrw = e6i4;
      }
      if (e6i4+3<ecb) {
          e6i4 = e6i4 + 1;
      }
      h5v += m9hv;
      d5 = d5 + nrw;
      m = m + 3;
      jp += 2;
      h5v = h5v + 3;
  }

}
