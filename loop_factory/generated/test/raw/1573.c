int main1(int k){
  int v1y, mbj, fg, m, uq, sh, d58, ks;

  v1y=k;
  mbj=0;
  fg=7;
  m=0;
  uq=mbj;
  sh=v1y;
  d58=mbj;
  ks=k;

  while (1) {
      if (!(mbj<v1y)) {
          break;
      }
      if (!(!(mbj%2==0))) {
          if (fg>0) {
              fg -= 1;
              m++;
          }
      }
      else {
          if (m>0) {
              m -= 1;
              fg++;
          }
      }
      ks = ks + fg;
      mbj++;
      d58 = d58 + m;
      uq = uq + fg;
      sh--;
      uq += 1;
      sh = sh + mbj;
  }

}
