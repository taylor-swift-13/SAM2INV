int main1(int a,int k){
  int r, g, d;

  r=(k%14)+14;
  g=0;
  d=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g % 4 == 0;
  loop invariant g >= 0;
  loop invariant d == 0 || d % 2 == 1;
  loop invariant d >= g/4;
  loop invariant r == (k % 14) + 14;
  loop invariant r == ((\at(k,Pre) % 14) + 14);
  loop invariant k == \at(k,Pre);
  loop invariant a == \at(a,Pre);

  loop invariant r == \at(k, Pre) % 14 + 14;


  loop invariant (d == 0) || (d % 2 == 1);
  loop invariant r == (\at(k, Pre) % 14) + 14;
  loop invariant d >= 0;
  loop invariant g <= r + 3;
  loop assigns d, g;
*/
while (g<r) {
      d = d+d;
      d = d+1;
      g = g+4;
  }

}
