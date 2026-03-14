int main1(int q,int n){
  int zdo, vk, yz, h9x, g, lr;

  zdo=q+20;
  vk=5;
  yz=0;
  h9x=0;
  g=-3;
  lr=-6;

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
