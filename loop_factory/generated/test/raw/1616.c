int main1(int a){
  int yr, cc, xha, bc0;

  yr=74;
  cc=1;
  xha=1;
  bc0=-5;

  while (1) {
      if (!(cc<=yr)) {
          break;
      }
      xha = xha+2*cc-1;
      a = a + xha;
      bc0 = bc0 + xha;
      cc = cc + 1;
  }

}
