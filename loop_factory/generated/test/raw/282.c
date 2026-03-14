int main1(){
  int j52f, u3zx, q, gd, r4, aste;

  j52f=1+22;
  u3zx=0;
  q=0;
  gd=0;
  r4=0;
  aste=4;

  while (u3zx<=j52f-1) {
      gd = u3zx%5;
      if (!(!(u3zx>=aste))) {
          r4 = (u3zx-aste)%5;
          q = q+gd-r4;
      }
      else {
          q = q + gd;
      }
      aste = aste + gd;
      u3zx += 1;
  }

}
