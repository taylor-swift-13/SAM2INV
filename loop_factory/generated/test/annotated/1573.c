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
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant sh == \at(k, Pre) + (mbj * (mbj - 1)) / 2;
  loop invariant 0 <= d58;
  loop invariant uq >= 0;
  loop invariant ks >= k;
  loop invariant 0 <= m <= 7;
  loop invariant 0 <= fg <= 7;
  loop invariant 0 <= mbj;
  loop invariant m + fg == 7;
  loop invariant sh == k + (mbj*(mbj - 1))/2;
  loop invariant mbj <= v1y || v1y < 0;
  loop invariant (uq - ks == mbj - k);
  loop invariant m == mbj % 2;
  loop invariant v1y == k;
  loop assigns m, fg, ks, mbj, d58, uq, sh;
*/
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