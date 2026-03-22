int main1(){
  int w5, x8, v42;

  w5=0;
  x8=(1%28)+10;
  v42=4;

  while (1) {
      if (!(x8>w5)) {
          break;
      }
      x8 -= w5;
      w5++;
      v42 = v42+(x8%8);
  }

}
