int main1(int k,int p){
  int r, j, v;

  r=54;
  j=r;
  v=j;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 2;
  loop invariant v >= 54;
  loop invariant r == 54;
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v - 54) % (j + 2) == 0;
  loop invariant j == 54;
  loop invariant j >= 3;
  loop invariant v % (j + 2) == 54 % (j + 2);
  loop invariant v >= j;
  loop invariant (v - j) % (j + 2) == 0;
  loop invariant j == r;
  loop assigns v;
*/
while (j>2) {
      v = v+2;
      v = v+j;
  }

}
