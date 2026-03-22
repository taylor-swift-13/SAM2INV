int main1(int e){
  int l4a, rmk, wq0, g0, vf, p, p8j, uv, lgo;

  l4a=e;
  rmk=0;
  wq0=3;
  g0=3;
  vf=0;
  p=4;
  p8j=0;
  uv=2;
  lgo=0;

  while (rmk<l4a) {
      if (rmk%3==0) {
          if (wq0>0) {
              wq0 -= 1;
              vf++;
          }
      }
      else {
          if (wq0<p) {
              wq0++;
              g0++;
          }
      }
      p += vf;
      p8j++;
      rmk = rmk + 1;
      lgo = lgo + g0;
      uv++;
      p = p + 3;
      uv += p;
  }

}
