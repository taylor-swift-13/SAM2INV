int main1(int a,int k){
  int r, g, d;

  r=(k%14)+14;
  g=r;
  d=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == (\at(k, Pre) % 14) + 14;
  loop invariant k == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant 0 <= g;
  loop invariant g <= r;
  loop invariant (g == r) ==> d == \at(k, Pre);
  loop invariant (g < r) ==> d >= 0;
  loop invariant g >= 0;
  loop invariant g <= ((\at(k,Pre) % 14) + 14);
  loop invariant r == ((\at(k,Pre) % 14) + 14);
  loop invariant r == \at(k, Pre) % 14 + 14;
  loop invariant r == (k % 14) + 14;
  loop invariant g <= (k % 14) + 14;
  loop assigns d, g;
*/
while (g>0) {
      d = d*2;
      d = d*d;
      g = g-1;
  }

}
