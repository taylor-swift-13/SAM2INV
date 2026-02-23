int main1(int a,int b){
  int p, i, e;

  p=(a%14)+4;
  i=p+4;
  e=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant p == (\at(a, Pre) % 14) + 4;
  loop invariant (i - p - 1) % 3 == 0;
  loop invariant p - 2 <= i;
  loop invariant i <= p + 4;
  loop invariant i >= p - 2;

  loop invariant e >= -5;
  loop invariant p == (a % 14) + 4;
  loop invariant a == \at(a, Pre) &&
                 b == \at(b, Pre) &&
                 p == (a % 14) + 4 &&
                 i >= p - 2 &&
                 i <= p + 4 &&
                 (e == -5 || e == 90 || e == 32580);
  loop invariant ((i - (p + 4)) % 3) == 0;
  loop invariant e % 5 == 0;
  loop assigns e, i;
*/
while (i>=p+1) {
      e = e*2;
      e = e*e+e;
      i = i-3;
  }

}
