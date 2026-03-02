int main1(int k,int m){
  int i, r, x, d;

  i=(k%6)+11;
  r=i;
  x=3;
  d=r;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == i;
  loop invariant d >= r;
  loop invariant k == \at(k,Pre);
  loop invariant m == \at(m,Pre);
  loop invariant x >= 3;
  loop invariant i == r;
  loop invariant r >= 4;
  loop invariant r == i && i == (k % 6) + 11;
  loop invariant d >= r && x >= 3;
  loop invariant (x == d*(d+1)) || (d == r && x == 3);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == (k % 6) + 11;
  loop invariant i == (k % 6) + 11;
  loop invariant r == i && d >= r;
  loop invariant x >= 0 && k == \at(k, Pre) && m == \at(m, Pre);
  loop invariant d >= (\at(k, Pre) % 6) + 11;
  loop invariant i == (\at(k, Pre) % 6) + 11;
  loop invariant r == (\at(k, Pre) % 6) + 11;
  loop assigns d, x;
*/
while (r>=4) {
      d = d+1;
      x = d*d;
      x = x+d;
  }

}
