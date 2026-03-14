int main1(int m){
  int gn6d, tq, xx;
  gn6d=9;
  tq=0;
  xx=gn6d;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre) + gn6d * tq - (tq * (tq + 1)) / 2;
  loop invariant xx == gn6d - tq;
  loop invariant gn6d == 9;
  loop invariant 0 <= tq <= gn6d;
  loop assigns xx, tq, m;
*/
while (1) {
      if (!(tq<gn6d&&xx>0)) {
          break;
      }
      xx--;
      tq++;
      m = (xx)+(m);
  }
}