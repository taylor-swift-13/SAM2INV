int main1(int a,int n){
  int h, k, v, i;

  h=56;
  k=2;
  v=a;
  i=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == \at(a, Pre) || v <= h;
  loop invariant (v == h) || ((v - \at(a, Pre)) % 4 == 0);
  loop invariant k <= h;
  loop invariant (v == \at(a, Pre) || v == h || (v >= \at(a, Pre) && v <= h && ((v - \at(a, Pre)) % 4) == 0));
  loop invariant k + 2 <= h + 1;
  loop invariant v <= h || v == \at(a, Pre);
  loop invariant h == 56;
  loop invariant k == 2;
  loop invariant ( \at(a, Pre) <= h ==> (v >= \at(a, Pre) && v <= h && ( (v - \at(a, Pre)) % 4 == 0 || v == h ) ) )
                   && ( \at(a, Pre) > h  ==> (v == \at(a, Pre) || v == h) );
  loop assigns v;
*/
while (k+2<=h) {
      if (v+4<=h) {
          v = v+4;
      }
      else {
          v = h;
      }
  }

}
