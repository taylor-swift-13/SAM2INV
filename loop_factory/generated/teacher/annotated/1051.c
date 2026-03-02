int main1(int b,int m){
  int j, v, y, p;

  j=40;
  v=4;
  y=-1;
  p=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 4;
  loop invariant v <= j;
  loop invariant b == \at(b, Pre) && m == \at(m, Pre);
  loop invariant 4 <= v && v <= j;
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant j == 40;
  loop invariant v >= 4 && v <= j && p < 0 && p % 2 == 0;
  loop invariant v >= 4 && v <= j && j == 40;
  loop invariant p % 4 == 0 && p <= -4;
  loop assigns p, v;
*/
while (v<=j-1) {
      p = p+p;
      v = v+1;
  }

}
