int main1(int d,int k){
  int e, rp, t, zl, my;

  e=73;
  rp=0;
  t=0;
  zl=0;
  my=d;

  while (1) {
      if (!(zl<e)) {
          break;
      }
      t += d;
      zl += 1;
      my = my+e-rp;
  }

  while (e!=0) {
      e = e - 1;
      my = my - 1;
      rp = rp + e;
  }

}
