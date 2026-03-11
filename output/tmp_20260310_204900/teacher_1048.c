int main1(int b,int k){
  int j, i, p, x;

  j=49;
  i=1;
  p=-2;
  x=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 1 && p >= -2 && p <= i - 3 && i >= 1;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre) && j == 49 && i <= 2*j;
  loop invariant x == 1 && p + 2 <= i && i >= 1;
  loop invariant b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant x == 1;

  loop invariant x == 1 && (p + 2) % x == 0 && i >= 1;

  loop invariant i >= 1;
  loop invariant p + 2 <= i;
  loop invariant p >= -2;
  loop invariant x == 1 && i >= 1 && p + 2 <= i;
  loop invariant p >= -2 && b == \at(b, Pre) && k == \at(k, Pre);
  loop invariant (i == 1) || (i % 2 == 0);
  loop invariant j == 49;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);

  loop invariant p + 2 >= 0;
  loop assigns p, i;
*/
while (i<j) {
      p = p+x;
      i = i*2;
  }
/*@
  assert !(i<j) &&
         (x == 1 && p >= -2 && p <= i - 3 && i >= 1);
*/


}
