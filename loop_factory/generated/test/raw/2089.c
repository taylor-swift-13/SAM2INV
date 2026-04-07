int main1(){
  int wr, vk, a8s, a4;

  wr=13;
  vk=wr;
  a8s=0;
  a4=wr;

  while (1) {
      if (vk>=wr) {
          break;
      }
      a8s = a8s + 3;
      vk = vk + 1;
      a4 = a4 + vk;
  }

}
