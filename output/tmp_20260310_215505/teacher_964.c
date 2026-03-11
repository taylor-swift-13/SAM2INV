int main1(int k,int q){
  int h, a, v, s;

  h=k+7;
  a=0;
  v=-2;
  s=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(k, Pre) + 7 && a >= 0;
  loop invariant h == k + 7;
  loop invariant (a <= h) || (h < 0);
  loop invariant 0 <= a;
  loop invariant v <= -2;
  loop invariant k == \at(k, Pre) && q == \at(q, Pre);
  loop invariant a >= 0;

  loop invariant q == \at(q, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (v - a) % 2 == 0;
  loop invariant a >= 0 && h == k + 7;

  loop invariant h == \at(k, Pre) + 7;
  loop invariant (2*v + 1) % 3 == 0;
  loop invariant 2*v + 1 < 0;

  loop invariant v <= -2 - 3*a;
  loop assigns a, v;
*/
while (a<=h-1) {
      v = v*3+1;
      a = a+1;
  }
/*@
  assert !(a<=h-1) &&
         (h == \at(k, Pre) + 7 && a >= 0);
*/


}
