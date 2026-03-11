int main1(){
  int f8, a6hi, q, j9, js;

  f8=4;
  a6hi=(1%18)+5;
  q=(1%15)+3;
  j9=a6hi;
  js=f8;

  while (1) {
      if (!(a6hi!=0)) {
          break;
      }
      a6hi--;
      j9 += f8;
      q = q - 1;
  }

  while (j9<f8) {
      js += 1;
      j9++;
      js += 1;
  }

}
