int main1(){
  int pp, sg, xtc, io, dx, pv, ttdj, n8o, xl0;

  pp=50;
  sg=0;
  xtc=sg;
  io=pp;
  dx=-8;
  pv=0;
  ttdj=8;
  n8o=pp;
  xl0=6;

  while (1) {
      if (!(sg < pp)) {
          break;
      }
      sg += 1;
      if (!(!((sg % 2) == 0))) {
          xtc += 1;
          xl0 = xl0 + 1;
      }
      else {
          io--;
          dx -= 1;
      }
      if (ttdj+6<pp) {
          ttdj = ttdj + 1;
      }
      n8o = n8o+io-io;
      pv = pv+ttdj+n8o;
      n8o += sg;
      pv += 1;
  }

}
