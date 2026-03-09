int main1(int s,int r){
  int b, vk, mi;

  b=(s%15)+6;
  vk=0;
  mi=-5;

  while (1) {
      if (!(vk<=b-1)) {
          break;
      }
      mi = b-vk;
      vk = vk + 1;
      s = s + vk;
  }

}
