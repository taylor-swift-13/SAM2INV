int main1(int b,int k){
  int l, i, a;

  l=(k%12)+13;
  i=0;
  a=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == k%12 + 13;
  loop invariant i % 3 == 0;

  loop invariant (i == 0) ==> (a == l);
  loop invariant (i > 0) ==> (a == 2*k - 10);
  loop invariant k == \at(k, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant 0 <= i && i <= l + 2;
  loop invariant i == 0 || a == 2 * \at(k, Pre) - 10;
  loop invariant l == (\at(k, Pre) % 12) + 13;
  loop invariant (i == 0) ==> (a == l) && (i > 0) ==> (a == 2*k - 10);
  loop invariant l == ((\at(k, Pre)) % 12) + 13;
  loop invariant l == (\at(k, Pre) % 12) + 13 &&
                   b == \at(b, Pre) &&
                   k == \at(k, Pre);

  loop invariant i >= 0 && i <= l + 2;
  loop invariant (i == 0 && a == l) || (i > 0 && a == 2*k - 10);
  loop assigns a, i;
*/
while (i<l) {
      a = k+(-5);
      a = a+a;
      i = i+3;
  }

}
