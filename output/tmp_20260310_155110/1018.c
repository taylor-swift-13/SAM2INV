int main1(int n,int p){
  int r, u, f, z;

  r=74;
  u=r;
  f=8;
  z=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == 74;
  loop invariant n == \at(n,Pre) && p == \at(p,Pre);
  loop invariant f >= 8;
  loop invariant f == 8 || f % 2 == 1;
  loop invariant u >= 0;
  loop invariant (f + 13) % 21 == 0;
  loop invariant u == r;
  loop invariant p == \at(p, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant u >= 0 && u <= 74;
  loop invariant (f == 8) || ((f - 13) % 2 == 0);
  loop invariant u == 74;
  loop invariant (f + 13) % 21 == 0 && f >= 8 && r == u;
  loop invariant u >= 0 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant ((f + 13) % 21) == 0 && (f + 13) > 0 && f >= 8;
  loop invariant r == 74 && u > 0 && n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && f >= 8;
  loop invariant (f + 13) % 21 == 0 && r == 74 && u == 74;
  loop invariant r == 74 && u == r && u >= 0;
  loop invariant f >= 8 && n == \at(n, Pre) && p == \at(p, Pre);
  loop assigns f;
*/
while (u>0) {
      f = f+4;
      f = f*2+5;
  }

}
