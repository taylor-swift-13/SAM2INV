int main1(){
  int lkon, x9, th9, ac, p, wnng, xv8t, vjva;

  lkon=1;
  x9=0;
  th9=x9;
  ac=lkon;
  p=lkon;
  wnng=lkon;
  xv8t=x9;
  vjva=-3;

  while (1) {
      if (!(x9 < lkon)) {
          break;
      }
      x9 = x9 + 1;
      if ((x9 % 2) == 0) {
          th9++;
      }
      else {
          ac++;
      }
      if ((x9%9)==0) {
          xv8t += 1;
      }
      p++;
      wnng += 2;
      vjva += ac;
      wnng += p;
  }

}
