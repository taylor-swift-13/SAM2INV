int main1(){
  int m, j7e, b, a, tt98;

  m=79;
  j7e=0;
  b=20;
  a=1;
  tt98=0;

  while (b>0&&a<=m) {
      if (b>a) {
          b = b - a;
      }
      else {
          b = 0;
      }
      tt98 = tt98 + 1;
      j7e++;
      a++;
  }

}
