int main15(int t){
  int zuwe, w2, jk, wlx, h5b, sx, cet;

  zuwe=t+16;
  w2=1;
  jk=(t%40)+2;
  wlx=0;
  h5b=t;
  sx=w2;
  cet=w2;

  while (1) {
      if (!(jk!=wlx)) {
          break;
      }
      wlx = jk;
      jk = (jk+zuwe/jk)/2;
      sx = sx+wlx-wlx;
      h5b = h5b+(wlx%7);
      t = t + 3;
      cet = cet + jk;
  }

}
