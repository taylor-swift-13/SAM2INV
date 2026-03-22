int main1(){
  int e3, xw, j, x;

  e3=(1%20)+1;
  xw=(1%25)+1;
  j=0;
  x=0;

  while (xw!=0) {
      if (xw%2==1) {
          j += e3;
          xw = xw - 1;
      }
      else {
      }
      xw = xw/2;
      e3 = 2*e3;
      x = x*4+(xw%7)+0;
      x = x*x+x;
  }

}
