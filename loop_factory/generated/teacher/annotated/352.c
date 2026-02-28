int main1(int b,int k){
  int h, u, e, y;

  h=(k%16)+6;
  u=0;
  e=0;
  y=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (k%16) + 6;

  loop invariant (e > 0) ==> (y == 2*h - 2*e + 2);
  loop invariant e >= 0;
  loop invariant (e > 0) ==> (y == 2*(h - (e - 1)));
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant (e > 0) ==> y == 2*(h - (e - 1));

  loop invariant h <= 21;
  loop assigns y, e;
*/
while (1) {
      y = h-e;
      e = e+1;
      y = y+y;
  }

}
