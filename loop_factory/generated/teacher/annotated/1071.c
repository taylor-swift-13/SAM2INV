int main1(int a,int b){
  int s, q, f, r;

  s=a;
  q=0;
  f=a;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == \at(a, Pre);
  loop invariant f >= \at(a, Pre);
  loop invariant f <= s + 1;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant s == a;
  loop invariant \at(a, Pre) <= f && f <= s + 1;
  loop invariant (f == s + 1) || ((f - \at(a, Pre)) % 3 == 0);
  loop invariant s == \at(a, Pre) && a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant f >= \at(a, Pre) && f <= s + 1;
  loop invariant a == \at(a, Pre) && b == \at(b, Pre);
  loop invariant s == a && (f == s || f == s+1);
  loop invariant f >= s;
  loop invariant f <= \at(a, Pre) + 1;
  loop invariant f == \at(a, Pre) || f == \at(a, Pre) + 1;
  loop invariant f >= a;
  loop assigns f;
*/
while (1) {
      if (f+2<=s) {
          f = f+2;
      }
      else {
          f = s;
      }
      f = f+1;
  }

}
