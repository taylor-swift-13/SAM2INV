int main1(){
  int n62, f, i, a4, r, bo6i, pr;

  n62=1;
  f=1;
  i=0;
  a4=0;
  r=0;
  bo6i=(1%18)+5;
  pr=n62;

  while (bo6i>=1) {
      i = i+1*1;
      a4 = a4+1*1;
      r = r+1*1;
      bo6i = bo6i - 1;
      pr = pr+(i%3);
  }

  while (f>=1) {
      bo6i = bo6i+1*1;
      a4 = a4+1*1;
      f--;
      r = r+1*1;
      bo6i = bo6i*bo6i+bo6i;
  }

}
