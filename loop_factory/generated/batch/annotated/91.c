int main1(int b,int k){
  int z, p, v, a;

  z=55;
  p=0;
  v=b;
  a=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant p % 2 == 0;

  loop invariant v == \at(b, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant z == 55;

  loop invariant v == b;
  loop invariant 0 <= p;
  loop invariant p <= z + 1;
  loop invariant p == 2*(p/2);
  loop invariant k == \at(k, Pre);

  loop invariant p >= 0;
  loop invariant (v == 8) ==> (a == -8);

  loop assigns a, p;
*/
while (p<z) {
      a = a+a;
      a = a+v;
      p = p+2;
  }

}
