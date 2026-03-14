int main1(){
  int g, tz7x, zgz, qhj, xi2, ko;

  g=73;
  tz7x=2;
  zgz=0;
  qhj=0;
  xi2=-3;
  ko=0;

  while (1) {
      if (!(qhj<=g-1)) {
          break;
      }
      qhj += 1;
      zgz += 1;
      xi2 = xi2 + tz7x;
      xi2 += ko;
  }

  while (tz7x>=2) {
      if (tz7x%2==0) {
          qhj = qhj + zgz;
      }
      else {
          qhj = qhj+zgz+1;
      }
      g = g+(qhj%4);
      tz7x = 1;
  }

}
