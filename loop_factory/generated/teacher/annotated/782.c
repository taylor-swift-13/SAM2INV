int main1(int a,int p){
  int i, w, b, z;

  i=a;
  w=0;
  b=a;
  z=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == a;
  loop invariant b == a + 4*w;
  loop invariant z == -3 + 3*w;
  loop invariant p == \at(p, Pre);
  loop invariant w >= 0;
  loop invariant i == \at(a, Pre);
  loop invariant b >= a;
  loop invariant z >= -3;
  loop invariant a == \at(a, Pre);
  loop assigns b, w, z;
*/
while (1) {
      b = b+4;
      z = z+3;
      w = w+1;
  }

}
