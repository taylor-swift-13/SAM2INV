int main1(){
  int x8m, z, to, fy, tqy;
  x8m=1+7;
  z=0;
  to=z;
  fy=z;
  tqy=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (fy == -z);
  loop invariant (to == -z);
  loop invariant (tqy == -z);
  loop invariant (0 <= z);
  loop invariant (z <= x8m);
  loop invariant (x8m == 1 + 7);
  loop assigns fy, to, z, tqy;
*/
while (z < x8m) {
      fy = (fy)+(-(1));
      to = to - 1;
      z += 1;
      tqy = tqy - 1;
  }
}