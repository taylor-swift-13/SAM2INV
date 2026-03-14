int main1(int q,int n){
  int zdo, vk, yz, h9x, g, lr;
  zdo=q+20;
  vk=5;
  yz=0;
  h9x=0;
  g=-3;
  lr=-6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zdo == \at(q,Pre) + 20;
  loop invariant h9x == yz*(yz+1)/2;
  loop invariant 0 <= yz <= 1;
  loop invariant g == -3 + 5*yz;
  loop invariant lr == -6 + yz*(zdo - 5);
  loop invariant q == \at(q,Pre) + yz*(zdo - 11);
  loop invariant vk == 5 + yz*(zdo - 5);
  loop assigns yz, g, lr, h9x, q, vk;
*/
while (1) {
      if (!(vk<zdo)) {
          break;
      }
      yz = yz + 1;
      g = g + vk;
      lr = lr+zdo-vk;
      h9x = h9x + yz;
      q += lr;
      vk = zdo;
  }
}