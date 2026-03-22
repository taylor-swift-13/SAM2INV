int main1(int s){
  int pz, y2d, cq, ay, x, a9n, t, rh;

  pz=s+23;
  y2d=pz;
  cq=0;
  ay=0;
  x=0;
  a9n=(s%18)+5;
  t=s;
  rh=y2d;

  while (1) {
      if (!(a9n>=1)) {
          break;
      }
      x = x+s*s;
      ay = ay+s*s;
      a9n--;
      cq = cq+s*s;
      if (s+6<pz) {
          s = s*s+rh;
      }
      if (t+3<pz) {
          t = t*rh;
      }
      rh += pz;
      t = t + y2d;
      rh = rh*rh;
  }

}
