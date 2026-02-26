int main1(int b,int k){
  int s, y, v, z;

  s=17;
  y=0;
  v=-5;
  z=1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v - 5*y == -5;
  loop invariant s == 17;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant y >= 0;
  loop invariant v == -5 + 5*y;
  loop invariant z == 1 + 4*y;
  loop assigns v, y, z;
*/
while (1) {
      v = v+5;
      z = z+4;
      y = y+1;
  }

}
