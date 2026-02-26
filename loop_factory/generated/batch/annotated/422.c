int main1(int k,int p){
  int r, j, v;

  r=54;
  j=r+3;
  v=-5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant j == r + 3;
  loop invariant v >= -5;
  loop invariant j - r == 3;
  loop invariant j == 57;
  loop invariant j >= r;
  loop invariant j >= r + 1;
  loop invariant v <= (v + 3) * (v + 3);
  loop assigns v;
*/
while (j-r>0) {
      v = v+3;
      if (k*k<=r+4) {
          v = v*v;
      }
  }

}
