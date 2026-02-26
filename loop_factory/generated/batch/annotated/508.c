int main1(int b,int k){
  int m, e, u, z;

  m=k;
  e=0;
  u=b;
  z=3;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u + 4*z == b + 12;
  loop invariant z <= 3;
  loop invariant u >= b;
  loop invariant (u - b) % 4 == 0;
  loop invariant m == k;
  loop invariant (u - \at(b, Pre)) % 4 == 0;
  loop invariant z == 3 - ((u - \at(b, Pre)) / 4);
  loop invariant (u - \at(b, Pre)) >= 0;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant u == b + 12 - 4*z;
  loop assigns u, z;
*/
while (1) {
      u = u+3;
      u = u+1;
      z = z-1;
  }

}
