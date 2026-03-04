int main1(int i){
  int b, w7, e;

  b=(i%37)+12;
  w7=b;
  e=-5;

  while (1) {
      if (!(w7<b)) {
          break;
      }
      e = e + 3;
      w7 = w7 + 1;
      i += w7;
      if (w7+6<=e+b) {
          i = i - i;
      }
  }

}
