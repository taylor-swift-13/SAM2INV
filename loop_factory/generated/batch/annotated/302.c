int main1(int a,int k){
  int f, v, z;

  f=(a%22)+9;
  v=f;
  z=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v == f;
  loop invariant f == (a % 22) + 9;
  loop invariant z >= v;
  loop invariant (z - v) % 5 == 0;
  loop invariant z - v >= 0;
  loop invariant ((z - v) % 5) == 0;

  loop assigns z;
*/
while (v>2) {
      z = z+3;
      z = z+2;
  }

}
