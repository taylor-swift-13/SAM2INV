int main1(int q){
  int igb3, z, l, w1;
  igb3=27;
  z=0;
  l=0;
  w1=-4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == z*(z-1)/2;
  loop invariant 6*w1 == z*z*z + 41*z - 24;
  loop invariant 0 <= z <= igb3;
  loop assigns l, w1, z, q;
*/
while (z<igb3) {
      l += z;
      w1 += l;
      z += 1;
      w1 = w1 + 1;
      q += w1;
      w1 += 6;
  }
}