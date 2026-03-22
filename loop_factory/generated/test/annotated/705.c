int main1(int z){
  int mr, h, l2d, eg;
  mr=0;
  h=0;
  l2d=0;
  eg=(z%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l2d == mr;
  loop invariant h == l2d;
  loop invariant mr >= 0;
  loop invariant eg <= ((\at(z,Pre) % 18) + 5);
  loop invariant z >= \at(z,Pre);
  loop assigns l2d, mr, eg, h, z;
*/
while (eg>0) {
      l2d = l2d+z*z;
      mr = mr+z*z;
      eg--;
      h = h+z*z;
      z = z + mr;
  }
}