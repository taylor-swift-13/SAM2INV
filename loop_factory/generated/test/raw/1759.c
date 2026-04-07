int main1(){
  int kk1, c, dt, wm, gg;

  kk1=1;
  c=0;
  dt=0;
  wm=kk1;
  gg=c;

  while (c < kk1) {
      c = c + 1;
      dt += wm;
      gg += dt;
      wm = wm+(dt%4);
  }

}
