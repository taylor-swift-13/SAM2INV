int main1(int a,int q){
  int h, s, e;

  h=q;
  s=0;
  e=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 0;
  loop invariant h == q;
  loop invariant (e == 0) || (e == 3);

  loop invariant 0 <= e;
  loop invariant e <= 3;
  loop invariant e == 0 || e == 3;
  loop invariant h == \at(q, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant 0 <= e <= 3;
  loop assigns e;
*/
while (s+1<=h) {
      e = e+3;
      if (e+1<h) {
          e = e-e;
      }
      else {
          e = e-e;
      }
  }

}
