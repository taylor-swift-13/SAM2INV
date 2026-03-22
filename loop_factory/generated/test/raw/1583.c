int main1(int b,int f){
  int zu, hs, dzb, dj, q, i, vp, nvv;

  zu=f*2;
  hs=0;
  dzb=b;
  dj=11;
  q=-6;
  i=zu;
  vp=-1;
  nvv=6;

  while (hs<=zu-1) {
      dj += 1;
      dzb += 1;
      if (dj<b+4) {
          f += 4;
      }
      if ((hs%7)==0) {
          f = f + hs;
      }
      vp += dj;
      b += dj;
      i = i + 1;
      nvv = (i+vp)+(q);
      hs = zu;
      if (hs+5<=q+zu) {
          f = f + 1;
      }
  }

}
