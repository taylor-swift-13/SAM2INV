int main1(int a,int b){
  int h, p, t;

  h=b+13;
  p=0;
  t=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && h == b + 13;
  loop invariant p >= 0 && t >= -3;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && h == b + 13 && p >= 0 && t >= -3;
  loop invariant t >= -3;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant h == b + 13;
  loop invariant p >= 0;
  loop invariant h == \at(b, Pre) + 13;
  loop invariant (p % 7) >= 0 && (p % 7) <= 6;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && h == \at(b, Pre) + 13;
  loop invariant p >= 0 && (p % 7) >= 0 && (p % 7) <= 6;
  loop invariant h == \at(b, Pre) + 13 && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant p >= 0 && 0 <= p % 7 && p % 7 <= 6;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre) && p >= 0 && t >= -3;
  loop assigns p, t;
*/
while (1) {
      if ((p%7)==0) {
          t = t*t+t;
      }
      p = p+1;
  }

}
