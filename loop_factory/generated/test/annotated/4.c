int main1(int a,int l,int z){
  int gz4, b20, qw;
  gz4=z+20;
  b20=2;
  qw=b20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qw == 2*(b20 - 1);
  loop invariant a == \at(a, Pre) + (b20 - 2);
  loop invariant z == \at(z, Pre) + (b20 - 2) * gz4;
  loop invariant gz4 == \at(z, Pre) + 20;
  loop invariant b20 >= 2;
  loop invariant l == \at(l, Pre);
  loop invariant 2 <= b20;
  loop invariant qw == 2*b20 - 2;
  loop invariant z == \at(z, Pre) + gz4*(b20 - 2);
  loop assigns qw, b20, z, a;
*/
while (1) {
      if (!(b20<gz4)) {
          break;
      }
      qw += 2;
      b20++;
      z = z + gz4;
      a++;
  }
}