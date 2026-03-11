int main1(int z){
  int u8, upw, at7;

  u8=(z%7)+11;
  upw=2;
  at7=z;

  while (1) {
      at7 += z;
      upw = upw + 1;
      if (upw>=u8) {
          break;
      }
  }

}
