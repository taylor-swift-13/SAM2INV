int main1(int y){
  int lq, zd, jg, c;
  lq=y*3;
  zd=lq;
  jg=0;
  c=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zd == lq;
  loop invariant lq == 3 * \at(y, Pre);
  loop invariant 1 <= c && (lq < 1 || c <= lq + 1);
  loop invariant (zd % 2 == 0 ==> jg == (c - 1)) && (zd % 2 != 0 ==> jg == -(c - 1));
  loop invariant ((zd % 2 == 0) ==> (jg == (c - 1))) &&
                   ((zd % 2 != 0) ==> (jg == -(c - 1)));
  loop assigns jg, c;
*/
while (c<=lq) {
      if (!(!(zd%2==0))) {
          jg += 1;
      }
      else {
          jg = jg - 1;
      }
      c = c + 1;
  }
}