int main1(int b,int k){
  int f, n, q;

  f=k+18;
  n=0;
  q=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre) && b == \at(b, Pre);
  loop invariant f == \at(k, Pre) + 18 && n >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant f == k + 18;
  loop invariant n >= 0;
  loop invariant n > 0 ==> q >= 0;
  loop invariant (n == 0) ==> (q == b);
  loop invariant (n > 0) ==> (q >= 0);
  loop invariant f == \at(k, Pre) + 18;
  loop invariant (n == 0) ==> (q == \at(b, Pre));
  loop invariant n == 0 ==> q == \at(b, Pre);
  loop invariant b == \at(b, Pre) && k == \at(k, Pre) && f == \at(k, Pre) + 18 && n >= 0;
  loop invariant (n == 0) ==> (q == \at(b, Pre)) && (n > 0) ==> (q >= 0);
  loop assigns q, n;
*/
while (1) {
      q = q*q;
      n = n+1;
  }

}
