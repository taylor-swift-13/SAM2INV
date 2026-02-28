int main1(int k,int p){
  int j, y, v, s;

  j=44;
  y=j;
  v=0;
  s=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant s == -2;
  loop invariant 0 <= v;
  loop invariant v <= j;
  loop invariant (j - v) % 2 == 0;
  loop invariant j == 44;
  loop invariant v % 2 == 0;
  loop invariant v >= 0;
  loop assigns v, s;
*/
while (v<j) {
      if (v<j) {
          v = v+1;
      }
      v = v+1;
      s = s-1;
      s = s+1;
  }

}
