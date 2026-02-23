int main1(int b){
  int p, z, v;

  p=b;
  z=p;
  v=z;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant p == b;
  loop invariant z <= p;
  loop invariant (p - z) % 2 == 0;
  loop invariant p == \at(b, Pre);
  loop invariant v == 0 || v == \at(b, Pre);
  loop invariant (v == \at(b, Pre)) <==> (z == \at(b, Pre));
  loop invariant z <= \at(b, Pre);
  loop invariant z % 2 == \at(b, Pre) % 2;
  loop invariant z >= v;
  loop invariant v <= p;

  loop invariant v <= z;
  loop invariant ((\at(b, Pre) - z) % 2 == 0);
  loop assigns v, z;
*/
while (z>1) {
      v = v-v;
      z = z-2;
  }

}
