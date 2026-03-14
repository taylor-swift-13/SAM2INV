int main1(int v){
  int yz, b;

  yz=v+12;
  b=0;

  while (1) {
      b += 1;
      if (b>=yz) {
          break;
      }
  }

  while (1) {
      if (!(b<=yz-8)) {
          break;
      }
      b += 8;
  }

}
