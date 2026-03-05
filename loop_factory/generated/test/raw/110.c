int main1(){
  int pp3, yqr, jj, o908;

  pp3=(1%10)+20;
  yqr=0;
  jj=0;
  o908=0;

  while (yqr<pp3) {
      jj += 1;
      o908 += 1;
      if (o908>=2) {
          o908 -= 2;
          jj += 1;
      }
      yqr = yqr + 1;
  }

}
