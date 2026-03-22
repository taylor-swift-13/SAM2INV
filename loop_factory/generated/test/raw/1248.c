int main1(int j){
  int tgk, yi, n5f, b7, fir;

  tgk=48;
  yi=0;
  n5f=1;
  b7=1;
  fir=j;

  while (1) {
      if (!(n5f<=tgk)) {
          break;
      }
      yi++;
      b7 += 2;
      n5f = n5f + b7;
      fir = fir+n5f+n5f;
      j++;
  }

}
