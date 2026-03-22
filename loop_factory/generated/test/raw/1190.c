int main1(){
  int by, tb, t, j5;

  by=(1%28)+8;
  tb=(1%22)+5;
  t=0;
  j5=0;

  while (tb!=0) {
      if (tb%2==1) {
          t = t + by;
          tb -= 1;
      }
      tb = tb/2;
      by = 2*by;
      j5 += tb;
  }

}
