int main1(int e,int z){
  int v1, u, uy, u8, w1;
  v1=76;
  u=0;
  uy=0;
  u8=0;
  w1=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= uy;
  loop invariant uy <= v1;
  loop invariant e == \at(e,Pre) + 2*uy;
  loop invariant u == uy * \at(e,Pre) + uy * (uy - 1);
  loop invariant w1 == \at(e,Pre) + uy*(uy+1)/2;
  loop invariant v1 == 76;
  loop assigns u, uy, e, w1;
*/
while (uy<v1) {
      u = u + e;
      uy++;
      e += 2;
      w1 += uy;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u8;
  loop assigns v1, z, u8, u;
*/
while (u<uy) {
      v1 = v1+u8*u;
      z = z+(v1%7);
      u8 += 1;
      u = uy;
  }
}