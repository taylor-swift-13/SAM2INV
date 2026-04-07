int main1(){
  int jg, x3, d, tv, jc;

  jg=1;
  x3=0;
  d=0;
  tv=x3;
  jc=x3;

  while (1) {
      if (!(x3 < jg)) {
          break;
      }
      d = d - jc;
      tv = tv + jc;
      x3 = x3 + 1;
      jc += tv;
  }

}
