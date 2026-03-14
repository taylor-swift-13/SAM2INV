int main1(int a,int s){
  int qe, x, gu1, ps31, ck, g;
  qe=a*4;
  x=0;
  gu1=0;
  ps31=0;
  ck=0;
  g=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gu1 == a * ps31;
  loop invariant ck == 0;
  loop invariant x == 0;
  loop invariant a == \at(a, Pre);
  loop invariant qe == 4 * \at(a, Pre);
  loop invariant ps31 >= 0;
  loop assigns gu1, ps31, a, ck;
*/
while (1) {
      if (!(ps31<=qe-1)) {
          break;
      }
      gu1 = gu1 + a;
      ps31 = ps31 + 1;
      a += x;
      ck += x;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ck == 0;
  loop invariant qe == 4 * a;
  loop assigns g, gu1, ps31, x;
*/
while (g<ck) {
      g++;
      gu1 = gu1+ck-qe;
      ps31 = ps31 + a;
      x += qe;
  }
}